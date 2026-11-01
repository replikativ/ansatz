"""The optional source-loaded module declares pinned core and Pattern dependencies."""
import xml.etree.ElementTree as ET


def validate(data, core_version):
    pom = ET.fromstring(data)
    ns = {'m': 'http://maven.apache.org/POM/4.0.0'}
    # A profile or dependencyManagement entry must not hide an optional compiler
    # dependency from a classpath test that supplies jars explicitly.
    dependencies = list(pom.iter('{http://maven.apache.org/POM/4.0.0}dependency'))
    coordinates = [(dep.findtext('m:groupId', namespaces=ns),
                    dep.findtext('m:artifactId', namespaces=ns),
                    dep.findtext('m:version', namespaces=ns)) for dep in dependencies]
    expected = [('org.replikativ', 'ansatz', core_version), ('org.replikativ', 'pattern', '1.0.452')]
    if sorted(coordinates) != sorted(expected):
        raise AssertionError('optional POM must declare exactly pinned core and Pattern: ' + str(coordinates))
    if any(node.tag.rsplit('}', 1)[-1] in {'systemPath', 'local/root'} for node in pom.iter()):
        raise AssertionError('local-path POM dependency')
