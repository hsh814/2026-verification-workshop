(* Module Cell.
  private cv = 0;
  def set(v) =
    cv := v;
  def get() =
    ret cv;
End Cell

(* client *)
Cell.set(42)
foo(); (* Cell.set() 안부름 *)
x = Cell.get();
assert(x=42); *)

(* 
refines
Module CellAbs.
    def set(v0) =
        v0 <- trigger (Take(nat));;
        trigger (Assume(cell(v0)));;
        trigger (Guarantee(cell(v0)));;
        Ret ()
    def get() =
        v0 <- trigger (Take(nat));;
        trigger (Assume(cell(v0)));;
        r <- trigger (Choose(nat));;
        trigger (Guarantee(r = v0 * cell(v0)));;;
        Ret r
End CellAbs. *)