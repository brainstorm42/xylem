"""Index canonical ProofBrick manifests without inventing source attribution."""
import json
import re
from collections import Counter
from pathlib import Path

import yaml

REQUIRED_RECORDS = (
    'README.md', 'provenance/source.md', 'provenance/dependencies.md',
    'provenance/acceptance.md', 'correspondence/notation.md',
    'correspondence/source_to_lean.md', 'correspondence/discrepancies.md',
)
STATUSES = {'proved_in_full', 'given_assumptions', 'conditional', 'supported',
            'paper_only', 'conventional_only', 'open'}


def _row(nid, kind, name, **kwargs):
    base = dict(id=nid, kind=kind, name=name, module=None, decl_kind=None,
                docstring=None, src_file=None, src_start=None, src_end=None,
                signature=None, is_external=0, props=None, rank=None)
    base.update(kwargs)
    return base


def parse_catalogue(root, bibliography, nodes, edges):
    """Preserve missing records/declarations/sources as explicit issues, not edges."""
    root, bibliography = Path(root), Path(bibliography)
    if not root.is_dir():
        return {'bricks': 0, 'issues': [f'canonical Brick directory missing: {root}']}
    bibtext = bibliography.read_text() if bibliography.is_file() else ''
    # Keys and source locators only. Do not pretend to parse arbitrary BibTeX fields.
    entries = list(re.finditer(r'(?m)^@\w+\s*\{\s*([^,\s]+)\s*,', bibtext))
    bibkeys = {m.group(1): 1 + bibtext[:m.start()].count('\n') for m in entries}
    ambiguous_keys = {key for key, count in Counter(m.group(1) for m in entries).items() if count > 1}
    manifests = sorted(root.glob('*/README.md'))
    report = {'bricks': len(manifests), 'issues': []}
    for manifest in manifests:
        body = manifest.read_text()
        parts = body.split('---', 2)
        if len(parts) < 3 or parts[0].strip():
            report['issues'].append(f'{manifest}: missing frontmatter')
            continue
        try:
            fm = yaml.safe_load(parts[1])
        except yaml.YAMLError as error:
            report['issues'].append(f'{manifest}: invalid frontmatter: {error}')
            continue
        if not isinstance(fm, dict) or fm.get('kind') != 'brick':
            report['issues'].append(f'{manifest}: expected a Brick manifest')
            continue
        brick_id = fm.get('brick_id')
        if brick_id != manifest.parent.name:
            report['issues'].append(f'{manifest}: brick_id must match its directory')
            continue
        issues = []
        for field in ('status', 'result_kind', 'mathematical_acceptance', 'lean_declarations',
                      'lean_modules', 'source_keys', 'application_interfaces'):
            if field not in fm:
                issues.append(f'missing manifest field: {field}')
        for field in ('lean_declarations', 'lean_modules', 'source_keys', 'internal_bricks',
                      'application_interfaces'):
            if not isinstance(fm.get(field, []), list) or any(
                    not isinstance(x, str) for x in fm.get(field, [])):
                issues.append(f'{field} must be a list of strings')
                fm[field] = []
        if fm.get('status') not in STATUSES:
            issues.append('unknown or missing status')
        missing_files = [name for name in REQUIRED_RECORDS
                         if not (manifest.parent/name).is_file()]
        if missing_files:
            issues.append('missing records: ' + ', '.join(missing_files))
        declarations = fm.get('lean_declarations', [])
        missing_declarations = [name for name in declarations
                                if f'decl:{name}' not in nodes
                                or nodes[f'decl:{name}']['is_external']]
        if missing_declarations:
            issues.append('unindexed declarations: ' + ', '.join(missing_declarations))
        missing_sources = [key for key in fm.get('source_keys', []) if key not in bibkeys]
        if missing_sources:
            issues.append('missing bibliography keys: ' + ', '.join(missing_sources))
        ambiguous_sources = sorted(set(fm.get('source_keys', [])) & ambiguous_keys)
        if ambiguous_sources:
            issues.append('ambiguous duplicate bibliography keys: ' + ', '.join(ambiguous_sources))
        missing_bricks = [name for name in fm.get('internal_bricks', [])
                          if not (root/name/'README.md').is_file()]
        if missing_bricks:
            issues.append('missing internal Bricks: ' + ', '.join(missing_bricks))
        nid = 'brick:' + brick_id
        heading = next((line[2:] for line in parts[2].splitlines() if line.startswith('# ')), brick_id)
        metadata = {key: fm.get(key) for key in ('status', 'result_kind', 'mathematical_acceptance',
                    'source_keys', 'lean_modules', 'lean_declarations', 'internal_bricks',
                    'application_interfaces', 'brick_level', 'level_reason', 'summary',
                    'keywords', 'interface')}
        metadata.update(canonical=True, manifest=str(manifest), issues=issues,
                        record_files_complete=not missing_files,
                        references_resolved=not missing_declarations and not missing_sources and not ambiguous_sources,
                        # Mechanical completeness is not mathematical acceptance.
                        resolved=not issues)
        # Reader interfaces are searchable authored metadata. They never create
        # formal dependency edges; those still come from the Lean extraction.
        search_text = [heading]
        for key in ('summary', 'brick_level'):
            if isinstance(fm.get(key), str):
                search_text.append(fm[key])
        keywords = fm.get('keywords', [])
        if isinstance(keywords, list):
            search_text.extend(x for x in keywords if isinstance(x, str))
        interface = fm.get('interface')
        if isinstance(interface, dict):
            for key in ('inputs', 'assumptions'):
                values = interface.get(key, [])
                if isinstance(values, list):
                    search_text.extend(x for x in values if isinstance(x, str))
            for output in interface.get('outputs', []) if isinstance(interface.get('outputs'), list) else []:
                if isinstance(output, dict) and isinstance(output.get('statement'), str):
                    search_text.append(output['statement'])
        nodes[nid] = _row(nid, 'brick', brick_id, docstring='\n'.join(search_text),
                         src_file=str(manifest), src_start=1, props=json.dumps(metadata))
        for name in declarations:
            if name not in missing_declarations:
                edges.append((f'decl:{name}', nid, 'BRICK_OF',
                              json.dumps({'origin': str(manifest), 'evidence': 'declared_manifest'})))
        for key in fm.get('source_keys', []):
            sid = f'src:{key}'
            nodes[sid] = _row(sid, 'source', key, src_file=str(bibliography),
                             src_start=None if key in ambiguous_keys else bibkeys.get(key), props=json.dumps({
                                 'bibliography': str(bibliography), 'entry_key': key,
                                 'entry_found': key in bibkeys, 'entry_ambiguous': key in ambiguous_keys}))
            # Keep the declared citation even when bibliography metadata is missing.
            edges.append((nid, sid, 'CITES', json.dumps({
                'origin': str(manifest), 'evidence': 'declared_citation',
                'entry_found': key in bibkeys, 'entry_ambiguous': key in ambiguous_keys})))
        report['issues'].extend(f'{brick_id}: {issue}' for issue in issues)
    # Manifest dependencies are provenance, not Lean proof-dependency edges.
    # Resolve after all manifests have been parsed so order cannot hide targets.
    for nid, row in list(nodes.items()):
        if row['kind'] != 'brick' or not row.get('props'):
            continue
        metadata = json.loads(row['props'])
        if not metadata.get('canonical'):
            continue
        for target in metadata.get('internal_bricks') or []:
            target_id = 'brick:' + target
            if target_id not in nodes:
                issue = f'unindexed internal Brick: {target}'
                metadata['issues'].append(issue)
                metadata['resolved'] = False
                metadata['references_resolved'] = False
                report['issues'].append(f'{row["name"]}: {issue}')
            else:
                edges.append((nid, target_id, 'BRICK_DEPENDS_ON', json.dumps({
                    'origin': metadata['manifest'], 'evidence': 'declared_manifest'})))
        row['props'] = json.dumps(metadata)
    return report
