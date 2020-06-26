// Specialize the accesstype for memory

/*
 * We can indicate to the MMU/PTW whether a memory operation conveys a
 * certainly cleared tag (Data) or a possibly asserted tag (Cap).  As the
 * MMU/PTW does not have access to the data paths, there is some possibility of
 * confusion.  Care must be taken to ensure that transactions marked as Data
 * are not used to convey asserted tags.  At the same time, tag-capable but
 * -clearing instructions should indicate that they are performing Data, not
 * Cap, operations to avoid spuriously raising CHERI page faults.  That is, if
 * reading a capability from memory but about to clear its tag, prefer to
 * indicate a Read(Data) to the MMU.  Similarly, if writing a capability with
 * known clear tag, indicate a Write(Data).
 */
enum ext_access_type = {
  Data,
  Cap
}

let default_write_acc : ext_access_type = Data

val accessType_to_str : AccessType(ext_access_type) -> string
function accessType_to_str (a) =
  match (a) {
    Read(Data)            => "R",
    Write(Data)           => "W",
    ReadWrite(Data, Data) => "RW",
    Read(Cap)             => "RC",
    Write(Cap)            => "WC",
    ReadWrite(Cap, Cap)   => "RCWC",
    ReadWrite(Data, Cap)  => "RWC",
    ReadWrite(Cap, Data)  => "RCW",
    Execute()             => "X"
  }

overload to_str = {accessType_to_str}
