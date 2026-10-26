import unittest
from pattern_contract import entries


class PatternNamespaceContract(unittest.TestCase):
    def test_root_only_source_and_aot_cannot_hide(self):
        for name in ['pattern.clj', 'pattern.cljc', 'pattern__init.class', 'pattern$fn__1.class']:
            with self.subTest(name=name):
                self.assertEqual({name}, entries([name]))

    def test_nested_sources_but_not_metadata_or_unrelated_names(self):
        self.assertEqual({'pattern/nanopass/dialect.clj'},
                         entries(['pattern/', 'pattern/nanopass/dialect.clj',
                                  'META-INF/pattern-profile/audit.json', 'patterned.clj']))
