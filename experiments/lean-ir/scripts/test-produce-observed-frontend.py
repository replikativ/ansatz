#!/usr/bin/env python3
"""Structural producer checks on actual exported companion rows; no guest run."""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("producer", Path(__file__).with_name("produce-observed-frontend.py"))
producer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(producer)


class LayoutChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = [json.loads(line) for line in (BUNDLE / "local-ir.jsonl").read_bytes().splitlines()][1:]
        cls.inventory = json.loads((BUNDLE / "headers.json").read_text())
        cls.contract = json.loads((producer.BASE / "research/java-ir-baseline/observed-frontend/contract.json").read_text())

    def check(self, rows=None, inventory=None):
        return producer.verify_layout(rows or self.rows, inventory or self.inventory, self.contract)

    def select(self, rows, suffix):
        return next(row for row in rows if producer.label(row["name"]) == producer.MODULE + suffix)

    def test_original_native_rows_and_layout(self):
        audit = self.check()
        self.assertEqual(len(self.rows), 16)
        self.assertEqual(audit["constructor"]["i"]["size"], 8)
        self.assertEqual(audit["constructor"]["i"]["ssize"], 4)
        self.assertEqual(len(audit["bool-stores"]), 4)

    def test_owned_gate_input_rejected(self):
        rows = copy.deepcopy(self.rows)
        self.select(rows, ".beforeElaboration")["ir"]["extern"]["xs"][2]["borrow"] = False
        with self.assertRaisesRegex(RuntimeError, "gate ABI"):
            self.check(rows)

    def test_changed_compiled_row_identity_rejected(self):
        inventory = copy.deepcopy(self.inventory)
        next(row for row in inventory if producer.label(row["name"]) == producer.MODULE + ".processCommandObserved")["sha256"] = "0" * 64
        with self.assertRaisesRegex(RuntimeError, "compiled row"):
            self.check(inventory=inventory)

    def test_parser_replay_or_missing_original_parser_rejected(self):
        rows = copy.deepcopy(self.rows)
        row = self.select(rows, ".processCommandObserved._lam_0")["ir"]["fdecl"]
        for node in walk(row):
            if isinstance(node, dict) and "fap" in node and producer.label(node["fap"]["c"]) == "Lean.Parser.parseCommand":
                node["fap"]["c"] = producer.typed_name("Other.parser")
        with self.assertRaisesRegex(RuntimeError, "call inventory"):
            self.check(rows)

    def test_missing_pre_elaboration_gate_rejected(self):
        rows = copy.deepcopy(self.rows)
        row = self.select(rows, ".processCommandObserved")["ir"]["fdecl"]
        for node in walk(row):
            if isinstance(node, dict) and "fap" in node and producer.label(node["fap"]["c"]) == producer.MODULE + ".beforeElaboration":
                node["fap"]["c"] = producer.typed_name("Other.gate")
        with self.assertRaisesRegex(RuntimeError, "call inventory"):
            self.check(rows)

    def test_observation_slot_inventory_rejected(self):
        rows = copy.deepcopy(self.rows)
        for node in walk(self.select(rows, ".processCommandObserved")["ir"]["fdecl"]):
            if isinstance(node, dict) and "ctor" in node and producer.label(node["ctor"]["i"]["name"]) == producer.MODULE + ".Observation.mk":
                node["ctor"]["i"]["size"] = 7
        with self.assertRaisesRegex(RuntimeError, "constructor layout"):
            self.check(rows)

    def test_observation_boolean_slot_alias_rejected(self):
        rows = copy.deepcopy(self.rows)
        for node in walk(self.select(rows, ".processCommandObserved")["ir"]["fdecl"]):
            if isinstance(node, list) and node and node[0] == "sset" and node[1] == {"idx": 59} and node[3] == 3:
                node[3] = 2
        with self.assertRaisesRegex(RuntimeError, "Boolean scalar"):
            self.check(rows)


def walk(root):
    todo = [root]
    while todo:
        value = todo.pop()
        yield value
        if isinstance(value, dict):
            todo.extend(value.values())
        elif isinstance(value, list):
            todo.extend(value)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", required=True, type=Path)
    args, rest = parser.parse_known_args()
    BUNDLE = args.bundle
    unittest.main(argv=[__file__] + rest)
