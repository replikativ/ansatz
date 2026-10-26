import unittest
from pom_contract import validate

HEAD = '<project xmlns="http://maven.apache.org/POM/4.0.0"><dependencies>'
TAIL = '</dependencies></project>'
CORE = '<dependency><groupId>org.replikativ</groupId><artifactId>ansatz</artifactId><version>0.2.test</version></dependency>'
PATTERN = '<dependency><groupId>org.replikativ</groupId><artifactId>pattern</artifactId><version>1.0.452</version></dependency>'


class DefaultPomContract(unittest.TestCase):
    def test_pinned_core_and_pattern(self):
        validate(HEAD + CORE + PATTERN + TAIL, '0.2.test')

    def test_missing_or_wrong_pattern_is_rejected(self):
        with self.assertRaises(AssertionError):
            validate(HEAD + CORE + TAIL, '0.2.test')
        with self.assertRaises(AssertionError):
            validate(HEAD + CORE + PATTERN.replace('1.0.452', '1.0.449') + TAIL, '0.2.test')

    def test_profile_cannot_hide_pattern(self):
        data = (HEAD + CORE + PATTERN + TAIL).replace('</project>',
            '<profiles><profile><dependencies>' + PATTERN + '</dependencies></profile></profiles></project>')
        with self.assertRaises(AssertionError):
            validate(data, '0.2.test')

    def test_duplicate_missing_or_wrong_core(self):
        for body in ['', CORE + CORE + PATTERN, CORE.replace('0.2.test', '0.2.other') + PATTERN]:
            with self.subTest(body=body), self.assertRaises(AssertionError):
                validate(HEAD + body + TAIL, '0.2.test')

    def test_local_path_is_never_published(self):
        with self.assertRaises(AssertionError):
            validate(HEAD + CORE.replace('</dependency>', '<systemPath>/tmp/core.jar</systemPath></dependency>') + PATTERN + TAIL,
                     '0.2.test')
