"""Source-scoped Markdown navigation for the generated Brick reading page.

This is not a mathematical Markdown translator. It changes only link targets,
reference labels and explicit anchors, adding source-qualified heading anchors.
Code, math and comments are protected. Unknown local fragments are findings,
not guessed targets. No dependency on a site-specific Markdown renderer.

Supported navigation is the flat-label Markdown subset: inline links/images,
full/collapsed/shortcut references and footnotes; backslash-escaped openings;
balanced or angle-delimited destinations; same-line quoted/parenthesized titles;
and reference destinations on the immediately following nonblank line, indented
or not. Preflight and rewriting share this recognition and the source mask.
Malformed recognized destinations/titles report blocking issues. This is not a
complete CommonMark parser (nested labels, multiline titles and container-block
grammars are outside this subset), nor an HTML sanitizer. Explicit HTML targets
and navigation cover lowercase a/img/h1-h6 with quoted, no-space-around-equals
attributes. Uniqueness checks cover these explicit targets, not renderer-created
implicit heading/footnote IDs. The final assembled page is checked as well as
each source. Excerpts retain source protection and reference scope; protected
block accounts are copied outside pipe cells and do not redefine source anchors.
"""

from __future__ import annotations

import html
import os
import re
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit


def source_anchor(name: str) -> str:
    return "source-" + re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")


def heading_slug(title: str) -> str:
    """GitHub-style heading fragment, before per-document deduplication."""
    title = re.sub(r"<[^>]*>", "", title)
    title = re.sub(r"\[([^]]+)\]\([^)]*\)", r"\1", title)
    title = html.unescape(title).lower()
    return re.sub(r"[^\w\s-]", "", title).replace(" ", "-")


def prose_mask(text: str, *, protected_spans: list[tuple[int, int]] | None = None) -> str:
    """Keep offsets/newlines while hiding code, comments and TeX math."""
    spans: list[tuple[int, int]] = []
    fence_start: int | None = None
    fence = ""
    offset = 0
    for line in text.splitlines(keepends=True):
        marker = re.match(r"^ {0,3}(`{3,}|~{3,})(.*)", line)
        if fence_start is not None:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence) and not marker[2].strip():
                spans.append((fence_start, offset + len(line)))
                fence_start = None
        elif marker:
            fence_start, fence = offset, marker[1]
        elif line.startswith(("    ", "\t")):
            spans.append((offset, offset + len(line)))
        offset += len(line)
    if fence_start is not None:
        spans.append((fence_start, len(text)))
    chars = list(text)

    def hide(start: int, end: int) -> None:
        if protected_spans is not None:
            protected_spans.append((start, end))
        chars[start:end] = ["\n" if c == "\n" else " " for c in text[start:end]]

    for start, end in spans:
        hide(start, end)
    # Run on the masked text so a delimiter inside a code fence cannot consume
    # subsequent prose. Order preserves code spans before dollar-delimited math.
    patterns = (r"<!--[\s\S]*?-->", r"(`+)(?!`)[\s\S]*?(?<!`)\1(?!`)",
                r"(?<!\\)\$\$[\s\S]*?(?<!\\)\$\$", r"\\\[[\s\S]*?\\\]",
                r"\\\([\s\S]*?\\\)", r"(?<![\\$])\$(?!\$)[\s\S]*?(?<!\\)\$(?!\$)")
    for pattern in patterns:
        for match in re.finditer(pattern, "".join(chars)):
            hide(*match.span())
    return "".join(chars)


@dataclass(frozen=True)
class Heading:
    start: int
    end: int
    level: int
    title: str
    fragment: str


class Document:
    def __init__(self, name: str, text: str):
        self.name, self.text = name, text
        self.anchor = source_anchor(name)
        protected_spans: list[tuple[int, int]] = []
        self.mask = prose_mask(text, protected_spans=protected_spans)
        self.protected_spans = protected_spans
        # Excerpts (including individual terminology cells) use the complete
        # source's label scope, not just definitions copied into that excerpt.
        self.references: dict[str, str] = {}
        for match in re.finditer(r"(?m)^ {0,3}\[([^]\n]+)\]:[ \t]*", self.mask):
            label = match[1]
            namespaced = self.anchor + "--ref-" + label.lstrip("^")
            if label.startswith("^"):
                namespaced = "^" + namespaced
            self.references[" ".join(label.casefold().split())] = namespaced
        self.headings: list[Heading] = []
        self.fragments: dict[str, str] = {}
        occupied: set[str] = set()
        candidates: list[tuple[int, int, int, str]] = []
        for match in re.finditer(r"(?m)^ {0,3}(#{1,6})[ \t]+(.+?)[ \t]*$", text):
            if not self.mask[match.start():match.end()].lstrip().startswith("#"):
                continue
            title = re.sub(r"\s+#+\s*$", "", match[2])
            candidates.append((match.start(), match.end(), len(match[1]), title))
        for match in re.finditer(r"(?m)^([^\n]+)\n {0,3}(=+|-+)[ \t]*$", text):
            # An unmasked thematic rule does not make a protected closing
            # delimiter above it a heading. Both lines must be prose candidates.
            title_mask = self.mask[match.start(1):match.end(1)]
            underline_mask = self.mask[match.start(2):match.end(2)]
            if title_mask.strip() and underline_mask == match[2] and not match[1].lstrip().startswith(("#", "|", "-")):
                candidates.append((match.start(), match.end(), 1 if match[2][0] == "=" else 2, match[1]))
        for start, end, level, title in sorted(candidates):
            # Even a partially visible line can begin inside multiline math or
            # code. Never insert an anchor before its protected closing token.
            if any(a < start < b for a, b in protected_spans):
                continue
            slug = heading_slug(title)
            fragment, count = slug, 0
            while fragment in occupied:
                count += 1
                fragment = f"{slug}-{count}"
            occupied.add(fragment)
            self.fragments[fragment] = f"{self.anchor}--{fragment}"
            self.headings.append(Heading(start, end, level, title, fragment))
        for match in re.finditer(r'<(?:a|h[1-6])\b[^>]*\b(?:id|name)=[\"\']([^\"\']+)[\"\'][^>]*>', self.mask):
            self.fragments[match[1]] = f"{self.anchor}--{match[1]}"

    def section_bounds(self, heading: Heading) -> tuple[int, int]:
        end = next((h.start for h in self.headings if h.start > heading.start and h.level <= heading.level), len(self.text))
        return heading.end, end


def _apply(text: str, edits: list[tuple[int, int, str]]) -> str:
    for start, end, value in sorted(edits, reverse=True):
        text = text[:start] + value + text[end:]
    return text


def _escaped(text: str, start: int) -> bool:
    before = start
    while before > 0 and text[before - 1] == "\\":
        before -= 1
    return (start - before) % 2 == 1


def _destination_end(text: str, start: int) -> int:
    if text[start:start + 1] == "<":
        end = text.find(">", start + 1)
        return end + 1 if end >= 0 and "\n" not in text[start:end] else start
    depth, end = 0, start
    while end < len(text):
        c = text[end]
        if c == "\\":
            end += 2
            continue
        if c.isspace() or (c == ")" and depth == 0):
            break
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        end += 1
    return end if depth == 0 else start


def _active_matches(pattern: str, text: str, mask: str):
    """Skip only an escaped opening, not later constructs inside its match."""
    position = 0
    compiled = re.compile(pattern)
    while match := compiled.search(mask, position):
        bracket = match.start() + int(match[0].startswith("!"))
        if _escaped(text, bracket):
            position = bracket + 1
            continue
        position = match.end()
        yield match


def _tail_end(text: str, start: int, *, inline: bool) -> int | None:
    """Consume an optional same-line title and the inline closing parenthesis."""
    position = start
    while position < len(text) and text[position] in " \t":
        position += 1
    if position > start and text[position:position + 1] in ('"', "'", "("):
        opening = text[position]
        closing = ")" if opening == "(" else opening
        position += 1
        depth = 1
        while position < len(text) and text[position] not in "\r\n":
            char = text[position]
            if char == "\\":
                position += 2
                continue
            if char == closing:
                depth -= 1
            elif opening == "(" and char == opening:
                depth += 1
            position += 1
            if depth == 0:
                break
        if depth:
            return None
        while position < len(text) and text[position] in " \t":
            position += 1
    if inline:
        return position + 1 if text[position:position + 1] == ")" else None
    return position if position == len(text) or text[position] in "\r\n" else None


@dataclass(frozen=True)
class NavigationToken:
    match: re.Match[str]
    kind: str
    end: int
    destination: tuple[int, int] | None = None


def navigation_tokens(text: str, mask: str, refs: dict[str, str]) -> tuple[list[NavigationToken], list[str]]:
    """Recognize the same whole constructs for rewriting and content preflight.

    Definitions accept a destination on the same or immediately following line,
    without a blank line; optional titles are on the destination line. Inline
    destinations allow balanced parentheses or angle delimiters, and titles allow
    quotes or balanced parentheses. Malformed recognized constructs fail closed.
    Footnote bodies remain prose, not link-only placeholders.
    """
    tokens: list[NavigationToken] = []
    issues: list[str] = []
    working = list(mask)

    def hide(start: int, end: int) -> None:
        working[start:end] = ["\n" if c == "\n" else " " for c in text[start:end]]

    for match in re.finditer(r"(?m)^ {0,3}\[([^]\n]+)\]:[ \t]*", mask):
        if match[1].startswith("^"):
            tokens.append(NavigationToken(match, "definition", match.end()))
            hide(*match.span())
            continue
        start = match.end()
        continuation = re.match(r"\r?\n[ \t]*", text[start:])
        if continuation:
            start += continuation.end()
        end = _destination_end(text, start)
        tail = _tail_end(text, end, inline=False) if end > start else None
        if tail is None:
            issues.append(f"missing or unsupported reference destination for {match[1]!r}")
            hide(*match.span())
            continue
        tokens.append(NavigationToken(match, "definition", tail, (start, end)))
        hide(match.start(), tail)
    for match in _active_matches(r"!?\[[^]\n]*\]\([ \t]*", text, "".join(working)):
        # Earlier links can contain bracket-like titles; do not parse them twice.
        if not working[match.start()].strip():
            continue
        start = match.end()
        end = _destination_end(text, start)
        tail = _tail_end(text, end, inline=True)
        if tail is None:
            issues.append(f"unsupported inline link destination or title at offset {match.start()}")
            hide(*match.span())
            continue
        tokens.append(NavigationToken(match, "inline", tail, (start, end)))
        hide(match.start(), tail)
    for match in _active_matches(r"\[([^]\n]+)\](?:\[([^]\n]*)\])?", text, "".join(working)):
        key = " ".join((match[2] or match[1]).casefold().split())
        if key in refs:
            tokens.append(NavigationToken(match, "reference", match.end()))
    return tokens, issues


def without_navigation(doc: Document) -> tuple[str, list[str]]:
    """Return content with whole active links/definitions blanked, not their tails."""
    tokens, issues = navigation_tokens(doc.text, doc.mask, doc.references)
    edits = []
    for token in tokens:
        start = token.match.start()
        if token.kind == "reference" and start > 0 and doc.text[start - 1] == "!" and not _escaped(doc.text, start - 1):
            start -= 1
        value = "".join("\n" if c == "\n" else " " for c in doc.text[start:token.end])
        edits.append((start, token.end, value))
    return _apply(doc.text, edits), issues


def authored_content(doc: Document) -> tuple[str, list[str]]:
    """Structural preflight uses the same protected headings as navigation.

    Code and math remain authored content. Comments, headings, list markers and
    recognized navigation do not supply a conventional account by themselves.
    Nonempty content is not a completeness or correctness assessment.
    """
    body, issues = without_navigation(doc)
    spans = [(h.start, h.end) for h in doc.headings]
    spans.extend((a, b) for a, b in doc.protected_spans if doc.text[a:b].startswith("<!--"))
    spans.extend(m.span() for m in re.finditer(r"(?m)^[ \t]*(?:[-+*]|\d+[.)])[ \t]+", doc.mask))
    chars = list(body)
    for start, end in spans:
        chars[start:end] = ["\n" if c == "\n" else " " for c in body[start:end]]
    return "".join(chars), issues


def duplicate_anchors(text: str, *, reserved: tuple[str, ...] = ()) -> list[str]:
    """Validate explicit targets in the supported HTML subset, ignoring literals."""
    anchors = set(reserved)
    issues = []
    for tag in re.finditer(r'<(?:a|img|h[1-6])\b[^>]*>', prose_mask(text)):
        # id and name on one element may identify the same target.
        values = {html.unescape(m[2]) for m in re.finditer(r'\b(?:id|name)=([\"\'])(.*?)\1', tag[0])}
        for value in sorted(values):
            if value in anchors:
                issues.append(f"duplicate final anchor {value!r}")
            anchors.add(value)
    return issues


class Embedding:
    def __init__(self, base: Path, sources: dict[str, str]):
        self.base = base.resolve()
        self.documents = {name: Document(name, text) for name, text in sources.items()}
        self.paths = {(self.base / name).resolve(): doc for name, doc in self.documents.items()}
        self.issues: list[str] = []

    def destination(self, name: str, value: str) -> str:
        angled = value.startswith("<") and value.endswith(">")
        raw = value[1:-1] if angled else value
        try:
            parsed = urlsplit(raw)
        except ValueError as error:
            self.issues.append(f"{name}: unsupported link destination {raw!r}: {error}")
            return value
        if parsed.scheme or parsed.netloc or raw.startswith("/"):
            return value
        path = (self.base / name).parent / unquote(parsed.path) if parsed.path else self.base / name
        target = self.paths.get(path.resolve())
        if target is not None and not parsed.query:
            fragment = unquote(parsed.fragment)
            if fragment and fragment not in target.fragments:
                self.issues.append(f"{name}: unresolved embedded fragment {raw!r}")
                return value
            result = "#" + (target.fragments[fragment] if fragment else target.anchor)
        else:
            result = quote(Path(os.path.relpath(path, self.base)).as_posix(), safe="/!$&'()*+,-.:;=@_~")
            if parsed.query:
                result += "?" + parsed.query
            if parsed.fragment:
                result += "#" + parsed.fragment
        return f"<{result}>" if angled else result

    def excerpt(self, name: str, start: int, end: int) -> tuple[str, bool]:
        """Rebase in source context before any table splitting or whitespace trim.

        The flag selects a block copy outside the pipe table for block code/math
        and multiline protected spans, whose delimiters and indentation must not
        be flattened. The complete source also remains in the source section.
        """
        doc = self.documents[name]
        requires_block = False
        for a, b in doc.protected_spans:
            if a < end and b > start:
                value = doc.text[a:b]
                if "\n" in value or value.startswith(("    ", "\t", "$$", "\\[")):
                    requires_block = True
        # Remove recognized headings only; regex stripping could delete code.
        edits = [(h.start - start, h.end - start, "") for h in doc.headings if start <= h.start and h.end <= end]
        text = _apply(doc.text[start:end], edits)
        mask = _apply(doc.mask[start:end], edits)
        return self.navigation(name, text, mask=mask, define_anchors=False), requires_block

    def navigation(self, name: str, text: str, *, mask: str | None = None, define_anchors: bool = True) -> str:
        """Rebase destinations and namespace per-source reference definitions."""
        mask = prose_mask(text) if mask is None else mask
        edits: list[tuple[int, int, str]] = []
        refs = self.documents[name].references
        tokens, issues = navigation_tokens(text, mask, refs)
        self.issues.extend(f"{name}: {issue}" for issue in issues)
        for token in tokens:
            match = token.match
            if token.destination is not None:
                start, end = token.destination
                edits.append((start, end, self.destination(name, text[start:end])))
            if token.kind == "inline":
                continue
            label = (match[2] or match[1]) if token.kind == "reference" else match[1]
            key = " ".join(label.casefold().split())
            namespaced = refs.get(key)
            if namespaced is None:
                self.issues.append(f"{name}: unsupported excerpt reference definition {label!r}")
                continue
            if token.kind == "definition":
                edits.append((*match.span(1), namespaced))
            elif label.startswith("^"):
                edits.append((match.start(), match.end(), f"[{namespaced}]"))
            else:
                edits.append((match.start(), match.end(), f"[{text[match.start(1):match.end(1)]}][{namespaced}]"))
        for match in re.finditer(r'<(?:a|img|h[1-6])\b[^>]*>', mask):
            tag = text[match.start():match.end()]
            for attr in re.finditer(r'\b(href|src|id|name)=([\"\'])(.*?)\2', tag):
                value = attr[3]
                if attr[1] in ("href", "src"):
                    value = self.destination(name, value)
                elif not define_anchors:
                    # Copies link to the full source's targets; they do not define
                    # a second target. Keep the element and all authored content.
                    edits.append((match.start() + attr.start(), match.start() + attr.end(), ""))
                    continue
                else:
                    value = self.documents[name].fragments.get(value, value)
                edits.append((match.start() + attr.start(3), match.start() + attr.end(3), value))
        return _apply(text, edits)

    def render(self, name: str) -> str:
        doc = self.documents[name]
        # Generated anchors are already source-qualified. The navigation pass
        # only namespaces original ids present in doc.fragments, leaving these
        # inserted targets unchanged.
        edits = [(h.start, h.start, f'<a id="{doc.fragments[h.fragment]}"></a>\n\n') for h in doc.headings]
        anchored = _apply(doc.text, edits)
        rendered = self.navigation(name, anchored)
        self.issues.extend(f"{name}: {issue}" for issue in duplicate_anchors(rendered, reserved=(doc.anchor,)))
        return rendered
