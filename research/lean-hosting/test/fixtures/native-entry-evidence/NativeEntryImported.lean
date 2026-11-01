import NativeEntryCases

namespace NativeEntryImported
abbrev ImportedArrow := NativeEntryCases.NatArrow
def viaImport : ImportedArrow := NativeEntryCases.aliasIdentity
def text (s : String) : String := NativeEntryCases.stringCase s
end NativeEntryImported
