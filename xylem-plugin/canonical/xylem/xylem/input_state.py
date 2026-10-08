"""Selected-input freshness and coverage; timestamps are provenance, not proof."""
import json
from pathlib import Path


def files_for(spec):
    files = {Path(spec[k]) for k in ('dot', 'extractor', 'bibliography', 'components') if spec.get(k)}
    for path in Path(spec['vault']).glob('*.md'):
        files.add(path)
    if spec.get('bricks'):
        files.update(Path(spec['bricks']).glob('*/*.md'))
        files.update(Path(spec['bricks']).glob('*/*/*.md'))
    if spec.get('ctrllib'):
        root = Path(spec['ctrllib'])
        files.update(root.joinpath('Ctrllib').rglob('*.lean'))
        files.update(root/name for name in ('Ctrllib.lean', 'Extract.lean', 'lean-toolchain',
                                          'lakefile.toml', 'lake-manifest.json'))
    if spec.get('source_root'):
        root = Path(spec['source_root'])
        files.update(path for path in root.rglob('*') if path.is_file() and '.lake' not in path.parts)
    return sorted(files)


def snapshot(spec):
    return {str(p.resolve()): {'mtime_ns': p.stat().st_mtime_ns, 'size': p.stat().st_size}
            if p.is_file() else None for p in files_for(spec)}


def extraction_issues(spec, nodes):
    source_key = 'source_root' if spec.get('source_root') else 'ctrllib'
    if not spec.get(source_key):
        return []
    root = Path(spec[source_key])
    if source_key == 'source_root':
        sources = [path for path in root.rglob('*') if path.is_file() and '.lake' not in path.parts]
        lean_sources = [path for path in root.rglob('*.lean')
                        if '.lake' not in path.parts and 'scripts' not in path.parts]
    else:
        sources = list(root.joinpath('Ctrllib').rglob('*.lean'))
        sources += [root/name for name in ('Ctrllib.lean', 'Extract.lean', 'lean-toolchain',
                                           'lakefile.toml', 'lake-manifest.json')]
        lean_sources = list(root.joinpath('Ctrllib').rglob('*.lean'))
    stamp = min(Path(spec[k]).stat().st_mtime_ns for k in ('dot', 'extractor'))
    newer = [str(p.relative_to(root)) for p in sources if p.is_file() and p.stat().st_mtime_ns > stamp]
    modules = {p.relative_to(root).with_suffix('').as_posix().replace('/', '.')
               for p in lean_sources}
    if source_key == 'ctrllib':
        modules = {name.replace('Ctrllib.', 'Ctrllib.', 1) for name in modules}
    indexed = {r['module'] for r in nodes.values() if r['kind'] == 'module'}
    issues = []
    if newer:
        issues.append('Lean inputs newer than extraction: ' + ', '.join(newer))
    if modules - indexed:
        issues.append('source modules absent from graph: ' + ', '.join(sorted(modules - indexed)))
    prefixes = ('Ctrllib.',) if source_key == 'ctrllib' else ('Percolation', 'Solution', 'Challenge')
    removed = {name for name in indexed if name and name.startswith(prefixes)} - modules
    if removed:
        issues.append('indexed modules without source files: ' + ', '.join(sorted(removed)))
    return issues


def current_warning(conn):
    exists = conn.execute("SELECT 1 FROM sqlite_master WHERE name='input_state'").fetchone()
    if not exists:
        return None  # Legacy databases keep their existing limited mtime check.
    row = conn.execute('SELECT payload FROM input_state WHERE id=1').fetchone()
    if row is None:
        return 'index input state is unavailable; rebuild Xylem'
    saved = json.loads(row['payload'])
    current = snapshot(saved['spec'])
    changed = sorted(path for path in set(saved['files']) | set(current)
                     if saved['files'].get(path) != current.get(path)
                     or (path in saved['files']) != (path in current))
    issues = list(saved['issues'])
    if changed:
        shown = ', '.join(changed[:8])
        if len(changed) > 8:
            shown += f' (and {len(changed)-8} more)'
        issues.append('selected inputs changed: ' + shown)
    if issues:
        if changed:
            advice = ('Selected inputs changed; rebuild Xylem after updating affected '
                      'extraction inputs. Lean-source changes require regeneration first.')
        elif any(issue.startswith('source modules absent from graph:') for issue in issues):
            advice = ('Extraction coverage is incomplete. Rebuilding an unchanged capture '
                      'cannot add omitted modules; use full regeneration for full coverage.')
        else:
            advice = 'Resolve extraction-input warnings before relying on current coverage.'
        return '; '.join(issues) + '. ' + advice
    return None
