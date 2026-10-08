-- xylem typed-property-graph store. Executed by build.py inside one transaction.
-- Edge direction convention (load-bearing): src depends-on / uses dst.

CREATE TABLE node (
  id          TEXT PRIMARY KEY,   -- 'mod:<module>' | 'decl:<fullname>' | 'wiki:<slug>' | 'src:<bibkey>' |
                                   -- 'brick:<module>:<bibkey>' (per-module) |
                                   -- 'brick:<module>.<theorem>:<bibkey|mathlib|new_result>' (per-theorem, yg3.41)
  kind        TEXT NOT NULL,      -- 'module' | 'declaration' | 'wiki_page' | 'brick' | 'source'
  name        TEXT NOT NULL,      -- full Lean name / module name / page slug / bibkey
  module      TEXT,               -- owning module (declaration, module, brick nodes); NULL for wiki/source
  decl_kind   TEXT,               -- 'theorem'|'def'|'abbrev'|'opaque'|'axiom'; NULL unless declaration
  docstring   TEXT,               -- extractor `doc` field; source paper title for 'source' nodes
  src_file    TEXT,               -- derived 'Ctrllib/X.lean' from module (contract v1 has no src_file)
  src_start   INTEGER,            -- 1-based start line (range.start[0])
  src_end     INTEGER,            -- 1-based end line (range.end[0])
  signature   TEXT,               -- JSON: {binders:[{name,binderInfo,type,tree}], conclusion, conclusion_tree, signature}
  is_external INTEGER DEFAULT 0,  -- 1 = defined outside Ctrllib (Mathlib OR core Lean/Init); stub node
  props       TEXT,               -- JSON: premises/axioms (decl); abbr/branch/status/sources (wiki);
                                   -- internal (stub); author/year/wiki_page (source). brick (two shapes):
                                   -- per-module (yg3.31) bibkey/resolved/n_sources -- resolved=false when
                                   -- its module cites >1 source and theorem_provenance: didn't claim every
                                   -- declaration; per-theorem (yg3.41) kind(paper|mathlib_derived|new_result)
                                   -- /resolved=true/per_theorem=true, plus bibkey (kind:paper) or
                                   -- mathlib_path (kind:mathlib_derived) -- always resolved, since it names
                                   -- exactly one declaration and one attribution from theorem_provenance:
  rank        REAL                -- PageRank, filled by the ranking pass
);
CREATE INDEX node_kind ON node(kind);
CREATE INDEX node_module ON node(module);
CREATE INDEX node_name ON node(name);

CREATE TABLE edge (
  src   TEXT NOT NULL REFERENCES node(id),
  dst   TEXT NOT NULL REFERENCES node(id),
  type  TEXT NOT NULL,   -- 'IMPORTS'|'USES_IN_TYPE'|'USES_IN_PROOF'|'DECLARED_IN'|'PAIRED_WITH'|'BRICK_OF'|'CITES'
  props TEXT,
  PRIMARY KEY (src, dst, type)
);
CREATE INDEX edge_src ON edge(src, type);
CREATE INDEX edge_dst ON edge(dst, type);

-- Derived, report-only structural features for local declarations.  Every
-- local declaration receives a row; unusable extractor trees remain visible
-- as status='skipped' with a named reason rather than a text fallback.
CREATE TABLE similarity_feature (
  decl_id          TEXT PRIMARY KEY REFERENCES node(id),
  schema_version   INTEGER NOT NULL,
  signature_sha256 TEXT NOT NULL,
  status           TEXT NOT NULL CHECK(status IN ('usable', 'skipped')),
  reason           TEXT,
  tree_size        INTEGER,
  features         TEXT
);
CREATE INDEX similarity_feature_status ON similarity_feature(status);
