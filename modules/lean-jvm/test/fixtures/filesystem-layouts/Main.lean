-- Native constructor/projection evidence for the pinned Lean runtime cohort.
-- These fixture wrappers are not original Lean runtime factories.
namespace RuntimeLayoutWitness
@[noinline] def systemTime (seconds : Int) (nanos : UInt32) : IO.FS.SystemTime :=
  ⟨seconds, nanos⟩
@[noinline] def metadata (accessed modified : IO.FS.SystemTime) (size : UInt64)
    (kind : IO.FS.FileType) (links : UInt64) : IO.FS.Metadata :=
  ⟨accessed, modified, size, kind, links⟩
@[noinline] def timeSeconds (time : IO.FS.SystemTime) : Int := time.sec
@[noinline] def timeNanos (time : IO.FS.SystemTime) : UInt32 := time.nsec
@[noinline] def fileAccessed (data : IO.FS.Metadata) : IO.FS.SystemTime := data.accessed
@[noinline] def fileModified (data : IO.FS.Metadata) : IO.FS.SystemTime := data.modified
@[noinline] def fileSize (data : IO.FS.Metadata) : UInt64 := data.byteSize
@[noinline] def fileKind (data : IO.FS.Metadata) : IO.FS.FileType := data.type
@[noinline] def fileLinks (data : IO.FS.Metadata) : UInt64 := data.numLinks
@[noinline] def error_alreadyExists (path : Option String) (code : UInt32) (details : String) : IO.Error :=
  .alreadyExists path code details
@[noinline] def error_invalidArgument (path : Option String) (code : UInt32) (details : String) : IO.Error :=
  .invalidArgument path code details
@[noinline] def error_permissionDenied (path : Option String) (code : UInt32) (details : String) : IO.Error :=
  .permissionDenied path code details
@[noinline] def error_resourceExhausted (path : Option String) (code : UInt32) (details : String) : IO.Error :=
  .resourceExhausted path code details
@[noinline] def error_inappropriateType (path : Option String) (code : UInt32) (details : String) : IO.Error :=
  .inappropriateType path code details
@[noinline] def error_noSuchThing (path : Option String) (code : UInt32) (details : String) : IO.Error :=
  .noSuchThing path code details
@[noinline] def error_otherError (code : UInt32) (details : String) : IO.Error :=
  .otherError code details
@[noinline] def error_resourceBusy (code : UInt32) (details : String) : IO.Error :=
  .resourceBusy code details
@[noinline] def error_resourceVanished (code : UInt32) (details : String) : IO.Error :=
  .resourceVanished code details
@[noinline] def error_unsupportedOperation (code : UInt32) (details : String) : IO.Error :=
  .unsupportedOperation code details
@[noinline] def error_hardwareFault (code : UInt32) (details : String) : IO.Error :=
  .hardwareFault code details
@[noinline] def error_unsatisfiedConstraints (code : UInt32) (details : String) : IO.Error :=
  .unsatisfiedConstraints code details
@[noinline] def error_illegalOperation (code : UInt32) (details : String) : IO.Error :=
  .illegalOperation code details
@[noinline] def error_protocolError (code : UInt32) (details : String) : IO.Error :=
  .protocolError code details
@[noinline] def error_timeExpired (code : UInt32) (details : String) : IO.Error :=
  .timeExpired code details
@[noinline] def error_interrupted (path : String) (code : UInt32) (details : String) : IO.Error :=
  .interrupted path code details
@[noinline] def error_noFileOrDirectory (path : String) (code : UInt32) (details : String) : IO.Error :=
  .noFileOrDirectory path code details
@[noinline] def error_unexpectedEof (_ : Unit) : IO.Error := .unexpectedEof
@[noinline] def error_userError (message : String) : IO.Error := .userError message
@[noinline] def optionSome (text : String) : Option String := some text
@[noinline] def optionNone (_ : Unit) : Option String := none
@[noinline] def ioSuccess (value : Nat) : IO Nat := pure value
@[noinline] def ioFailure (error : IO.Error) : IO Nat := throw error
@[noinline] def fileType_dir (_ : Unit) : IO.FS.FileType := .dir
@[noinline] def fileType_file (_ : Unit) : IO.FS.FileType := .file
@[noinline] def fileType_symlink (_ : Unit) : IO.FS.FileType := .symlink
@[noinline] def fileType_other (_ : Unit) : IO.FS.FileType := .other
end RuntimeLayoutWitness

def main : IO Unit := pure ()
