#!/usr/bin/env python3
"""Compile pinned hash.cpp/hash.h verbatim with minimal type/include scaffolding.

This is a compiled pinned hash-source arithmetic oracle, not the Lean runtime ABI.
No JVM, full Lean build, scheduler, heap, native value representation or FFI runs.
"""
import argparse
import hashlib
import json
import pathlib
import platform
import resource
import subprocess

PIN = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
PINS = {'src/runtime/hash.cpp': '9b677d0ef3d7f1dbcb9e6c019b15b2fec1fd0cbe112cd103655c56a8220ddfac',
        'src/runtime/hash.h': 'fe27044afcc40e24c69287cbd7c5b6ac4989221cdfb839dd00c8b3831609155a',
        'LICENSE': '8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e'}
MASK = (1 << 64) - 1
STRINGS = ['', 'a', 'a\0b', '1234567', '12345678', '123456789', 'éλ', '𐀀😀']
MIXES = [(0, 0), (1, 1), (1 << 63, MASK), (MASK, 1 << 63)]
SHIMS = {'runtime/debug.h': '#pragma once\n',
         'runtime/int.h': '#pragma once\n#include <cstdint>\n#include <cstddef>\nnamespace lean { using uint64 = std::uint64_t; using std::size_t; }\n'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def limited(memory, cpu):
    def apply():
        resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 5))
        resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 1024 * 1024,) * 2)
    return apply


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-source', required=True)
    parser.add_argument('--output', required=True, help='Ignored build directory')
    parser.add_argument('--cxx', default='g++')
    parser.add_argument('--python-reference', help='Optional source-derived vector JSON to cross-check')
    args = parser.parse_args()
    output = pathlib.Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    for source, expected in PINS.items():
        raw = subprocess.check_output(['git', '-C', args.lean_source, 'show', PIN + ':' + source])
        if digest(raw) != expected:
            raise ValueError('Pinned source hash mismatch: ' + source)
        target = output / ('LICENSE' if source == 'LICENSE' else source.removeprefix('src/'))
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
    for name, text in SHIMS.items():
        (output / name).write_text(text)
    driver = ['#include "runtime/hash.h"', '#include <iostream>', '#include <cstdint>',
              'int main() {', 'static_assert(sizeof(void*) == 8, "64-bit profile required");',
              'static_assert(sizeof(lean::uint64) == 8, "uint64 size");',
              'std::uint64_t one=1; if(*reinterpret_cast<unsigned char*>(&one)!=1) return 2;']
    for i, text in enumerate(STRINGS):
        raw = text.encode('utf-8', errors='strict')
        literal = ''.join('\\x%02x' % b for b in raw)
        driver.append('std::cout << "string\\t%d\\t" << lean::hash_str(%d, reinterpret_cast<unsigned char const*>("%s"), 11) << "\\n";' % (i, len(raw), literal))
    for i, (h, k) in enumerate(MIXES):
        driver.append('std::cout << "mix\\t%d\\t" << lean::hash(%dULL,%dULL) << "\\n";' % (i, h, k))
    driver.extend(['std::cout << "name\\t0\\t1723\\n";',
                   'std::cout << "name\\t1\\t" << lean::hash(1723,lean::hash_str(3,reinterpret_cast<unsigned char const*>("foo"),11)) << "\\n";',
                   'std::cout << "name\\t2\\t" << lean::hash(1723,18446744073709551615ULL) << "\\n";',
                   'std::cout << "name\\t3\\t" << lean::hash(1723,17) << "\\n";', 'return 0;', '}'])
    driver_bytes = ('\n'.join(driver) + '\n').encode()
    (output / 'driver.cpp').write_bytes(driver_bytes)
    version = subprocess.check_output([args.cxx, '--version'], text=True).splitlines()[0]
    command = [args.cxx, '-std=c++11', '-O2', '-I', str(output),
               str(output / 'runtime/hash.cpp'), str(output / 'driver.cpp'), '-o', str(output / 'oracle')]
    compiled = subprocess.run(command, capture_output=True, text=True, timeout=60,
                              preexec_fn=limited(256 * 1024 * 1024, 30))
    (output / 'compiler.stderr').write_text(compiled.stderr)
    if compiled.returncode:
        raise RuntimeError('Compiler failed: ' + compiled.stderr)
    executed = subprocess.run([str(output / 'oracle')], capture_output=True, text=True, timeout=10,
                              preexec_fn=limited(64 * 1024 * 1024, 5))
    executed.check_returncode()
    actual = {(kind, int(i)): value for kind, i, value in
              (line.split('\t') for line in executed.stdout.splitlines())}
    if len(actual) != len(STRINGS) + len(MIXES) + 4:
        raise ValueError('Unexpected oracle output')
    result = {'basis': 'compiled pinned hash-source arithmetic oracle; not full Lean runtime ABI',
              'lean-commit': PIN, 'upstream-source-sha256': PINS,
              'scaffolding-sha256': {name: digest(text.encode()) for name, text in SHIMS.items()},
              'driver-sha256': digest(driver_bytes), 'compiler': version,
              'compiler-flags': ['-std=c++11', '-O2'], 'host-machine': platform.machine(),
              'profile': {'pointer-bits': 64, 'uint64-bits': 64, 'byte-order': 'little'},
              'compiler-memory-limit-bytes': 256 * 1024 * 1024,
              'compiler-exit': compiled.returncode, 'oracle-exit': executed.returncode,
              'string': [{'text': s, 'utf8-hex': s.encode().hex(), 'hash': actual['string', i]} for i, s in enumerate(STRINGS)],
              'mix': [{'h': str(h), 'k': str(k), 'hash': actual['mix', i]} for i, (h, k) in enumerate(MIXES)],
              'name': [{'kind': kind, 'hash': actual['name', i]} for i, kind in enumerate(['anonymous', 'str-foo', 'num-max64', 'num-2^64-sentinel17'])]}
    if args.python_reference:
        reference_bytes = pathlib.Path(args.python_reference).read_bytes()
        reference = json.loads(reference_bytes)
        if reference['string'] != result['string'] or reference['mix'] != result['mix']:
            raise ValueError('Compiled/Python hash vector mismatch')
        if [v['hash'] for v in reference['name']] != [v['hash'] for v in result['name']]:
            raise ValueError('Compiled/Python Name hash vector mismatch')
        result['python-source-reference-sha256'] = digest(reference_bytes)
        result['matching-source-reference-vectors'] = len(actual)
    (output / 'results.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'compiler-exit': compiled.returncode, 'oracle-exit': executed.returncode,
                      'vectors': len(actual), 'results-sha256': digest((output / 'results.json').read_bytes())}))


if __name__ == '__main__':
    main()
