#!/usr/bin/env python3
"""Extract the pinned Longfellow mdoc test vectors used by eu-id tests."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

PINNED_COMMIT = "d8ad8f65187c7c364a3c2181ad484bcab03f0ec2"
DEFAULT_SOURCES = [
    Path("/private/tmp/longfellow-zk/lib/circuits/mdoc/mdoc_examples.h"),
    Path("/Users/lucas/longfellow-zk/lib/circuits/mdoc/mdoc_examples.h"),
]
DEFAULT_OUTPUT = Path("crates/eu-id-prover/tests/vectors")

VECTORS = {
    3: {
        "name": "longfellow_mdl3",
        "doc_type": "org.iso.18013.5.1.mDL",
        "namespace": "org.iso.18013.5.1",
        "description": "Sprind-Funke mDL with family_name, birth_date, issue_date, height, age_over_18",
    },
    11: {
        "name": "longfellow_euav11",
        "doc_type": "eu.europa.ec.av.1",
        "namespace": "eu.europa.ec.av.1",
        "description": "EU age-verification credential with age_over_18",
    },
}


def strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"//.*", "", text)


def split_entries(text: str) -> list[str]:
    start = text.index("static const struct MdocTests mdoc_tests[] = {")
    pos = text.index("{", start) + 1
    entries: list[str] = []
    depth = 0
    entry_start: int | None = None
    in_string = False
    escape = False
    line_comment = False
    block_comment = False
    i = pos
    while i < len(text):
        c = text[i]
        n = text[i + 1] if i + 1 < len(text) else ""
        if line_comment:
            if c == "\n":
                line_comment = False
            i += 1
            continue
        if block_comment:
            if c == "*" and n == "/":
                block_comment = False
                i += 2
                continue
            i += 1
            continue
        if in_string:
            if escape:
                escape = False
            elif c == "\\":
                escape = True
            elif c == '"':
                in_string = False
            i += 1
            continue
        if c == "/" and n == "/":
            line_comment = True
            i += 2
            continue
        if c == "/" and n == "*":
            block_comment = True
            i += 2
            continue
        if c == '"':
            in_string = True
            i += 1
            continue
        if c == "{":
            if depth == 0:
                entry_start = i
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0 and entry_start is not None:
                entries.append(text[entry_start : i + 1])
                entry_start = None
        i += 1
    return entries


def static_string(entry: str, index: int) -> str:
    matches = list(re.finditer(r"StaticString\s*\(", entry))
    pos = matches[index].end()
    depth = 1
    i = pos
    while i < len(entry):
        if entry[i] == "(":
            depth += 1
        elif entry[i] == ")":
            depth -= 1
            if depth == 0:
                inside = entry[pos:i]
                parts = re.findall(r'"([^"\\]*(?:\\.[^"\\]*)*)"', inside)
                return "".join(parts).encode("utf-8").decode("unicode_escape")
        i += 1
    raise ValueError("unterminated StaticString")


def brace_groups(entry: str) -> list[str]:
    text = strip_comments(entry)
    groups: list[str] = []
    stack: list[int] = []
    in_string = False
    escape = False
    for i, c in enumerate(text):
        if in_string:
            if escape:
                escape = False
            elif c == "\\":
                escape = True
            elif c == '"':
                in_string = False
            continue
        if c == '"':
            in_string = True
            continue
        if c == "{":
            stack.append(i)
        elif c == "}":
            start = stack.pop()
            groups.append(text[start : i + 1])
    return groups


def bytes_from_group(group: str) -> bytes:
    values: list[int] = []
    pattern = r"0x([0-9a-fA-F]{1,2})|(?<![A-Za-z0-9_])(\d+)(?![A-Za-z0-9_])"
    for match in re.finditer(pattern, group):
        if match.group(1):
            values.append(int(match.group(1), 16))
        else:
            value = int(match.group(2))
            if 0 <= value <= 255:
                values.append(value)
    return bytes(values)


def parse_entry(entries: list[str], index: int) -> dict[str, object]:
    entry = entries[index]
    cleaned = strip_comments(entry)
    groups = brace_groups(entry)
    doc_match = re.search(r"\n\s*(k[A-Za-z0-9_]+)\s*,\n\s*(\d+)\s*,\n\s*\{", cleaned)
    now_match = re.search(r'\(uint8_t\*\)"([^"]+)"', cleaned)
    if not doc_match or not now_match:
        raise ValueError(f"metadata parse failed for mdoc_tests[{index}]")
    transcript = bytes_from_group(groups[0])
    mdoc = bytes_from_group(groups[1])
    return {
        "index": index,
        "pkx": static_string(entry, 0),
        "pky": static_string(entry, 1),
        "transcript": transcript,
        "now": now_match.group(1),
        "doc_type_symbol": doc_match.group(1),
        "mdoc_size": int(doc_match.group(2)),
        "mdoc": mdoc,
    }


def write_vector(base: Path, source: Path, parsed: dict[str, object], spec: dict[str, str]) -> None:
    out = base / spec["name"]
    out.mkdir(parents=True, exist_ok=True)
    mdoc = parsed["mdoc"]
    transcript = parsed["transcript"]
    assert isinstance(mdoc, bytes)
    assert isinstance(transcript, bytes)
    (out / "mdoc.cbor").write_bytes(mdoc)
    (out / "transcript.bin").write_bytes(transcript)
    (out / "issuer_pk.json").write_text(
        json.dumps({"x": parsed["pkx"], "y": parsed["pky"]}, indent=2) + "\n",
        encoding="utf-8",
    )
    (out / "now.txt").write_text(str(parsed["now"]) + "\n", encoding="utf-8")
    (out / "doc_type.txt").write_text(spec["doc_type"] + "\n", encoding="utf-8")
    (out / "README.md").write_text(
        f"""# Longfellow mdoc vector: {spec["name"]}

Source: `{source}` at git commit `{PINNED_COMMIT}`.
Upstream: `https://github.com/google/longfellow-zk.git`.
License: Apache-2.0, copyright Google LLC.

These files are byte-for-byte extracts of the specified `mdoc_tests` entry.
Regenerate from the repository root with:

```bash
rtk proxy python3 tools/extract_longfellow_vectors.py --source {source}
```

- mdoc_tests index: `{parsed["index"]}`
- description: {spec["description"]}
- docType: `{spec["doc_type"]}`
- namespace: `{spec["namespace"]}`
- transcript bytes: `{len(transcript)}`
- DeviceResponse bytes: `{len(mdoc)}`
- now: `{parsed["now"]}`
- issuer public key x: `{parsed["pkx"]}`
- issuer public key y: `{parsed["pky"]}`
""",
        encoding="utf-8",
    )


def default_source() -> Path:
    for source in DEFAULT_SOURCES:
        if source.exists():
            return source
    return DEFAULT_SOURCES[0]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=default_source())
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    entries = split_entries(args.source.read_text(encoding="utf-8"))
    for index, spec in VECTORS.items():
        parsed = parse_entry(entries, index)
        if len(parsed["mdoc"]) != parsed["mdoc_size"]:
            raise ValueError((index, len(parsed["mdoc"]), parsed["mdoc_size"]))
        write_vector(args.output, args.source, parsed, spec)
        print(
            index,
            spec["name"],
            len(parsed["transcript"]),
            len(parsed["mdoc"]),
            parsed["now"],
        )


if __name__ == "__main__":
    main()
