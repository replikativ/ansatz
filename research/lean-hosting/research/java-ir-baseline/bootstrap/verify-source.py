#!/usr/bin/env python3
"""Bootstrap control-source audit only. No JVM, native tool or artifact restore."""
import hashlib, json, pathlib, re
P = pathlib.Path(__file__).resolve().parent
M = json.loads((P / "manifest.json").read_text())
assert M["schema"] == "source4-bootstrap-control-source/1"
owned = {str(f.relative_to(P)) for f in P.rglob("*")
         if f.is_file() and "__pycache__" not in f.parts
         and str(f.relative_to(P)) != "manifest.json"}
assert set(M["files"]) == owned
for name, expected in M["files"].items():
    file = P / name
    raw = file.read_bytes()
    assert len(raw) == expected["bytes"], name
    assert hashlib.sha256(raw).hexdigest() == expected["sha256"], name
    text = raw.decode("utf-8")
    if name != "verify-source.py":
        assert not re.search(r"/home/|/Users/|[A-Za-z]:\\Users\\", text), name
    if name.endswith(".clj"):
        stack, quoted, escaped, comment = [], False, False, False
        for i, c in enumerate(text):
            if comment:
                if c == "\n": comment = False
            elif quoted:
                if escaped: escaped = False
                elif c == "\\": escaped = True
                elif c == '"': quoted = False
            elif c == ";": comment = True
            elif c == '"': quoted = True
            elif c in "([{": stack.append(c)
            elif c in ")]}":
                assert stack and stack.pop() == {")": "(", "]": "[", "}": "{"}[c], (name, i)
        assert not stack and not quoted, name
source4 = (P / "source4.clj").read_text()
assert source4.count("(source/compose!") == 1
assert "with-redefs" not in source4 and "(eval" not in source4
assert "cohort/prepare-general-source-child!" in source4
assert "captured/open!" in source4 and "source/source-binding!" in source4
assert "cohort/open-companion!" in (P/"captured-runtime.clj").read_text()
assert "java-ir-baseline-checks" not in (P/"captured-runtime.clj").read_text()
assert "load-file" in (P/"definitions.clj").read_text()
assert "(eval" not in (P/"definitions.clj").read_text()
assert len(re.findall(r"^\(deftest ", (P/"models/artifacts.clj").read_text(), re.M)) == 8
assert len(re.findall(r"^\(deftest ", (P/"models/source4.clj").read_text(), re.M)) == 2
schema = json.loads((P/"profile.schema.json").read_text())
assert schema["properties"]["overlays"]["minItems"] == schema["properties"]["overlays"]["maxItems"] == 4
order = json.loads((P/"definition-order.json").read_text())
assert len(order["definitions"]) == 47
assert len(order["entry-namespaces"]) == 3
assert len({name for name, _ in order["definitions"]}) == 47
print(json.dumps({"owned-files": len(owned), "metadata-model-families": 10,
                  "source4-compose-sites": 1, "runtime-acceptance": M["runtime-acceptance"],
                  "JVM-or-native-executed": False, "dependencies": M["dependencies"]}))
