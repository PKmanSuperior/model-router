signature MACE =
sig
    val makeInFile: Form.form list -> int -> unit
    val runM4: unit -> string
    val mace: Form.form list -> int -> bool
end

structure Mace : MACE =
struct
local
    structure F = Form
    structure T = Term
in

fun renameFunTerm (T.Var x) = T.Var x
  | renameFunTerm (T.Fun (f, ts)) = if null ts then T.Fun ("$" ^ f, ts) else T.Fun (f, List.map renameFunTerm ts)

fun renameFun (F.Pred (p, ts)) = F.Pred (p, List.map renameFunTerm ts)
  | renameFun (F.Eq (l, r)) = F.Eq (renameFunTerm l, renameFunTerm r)
  | renameFun (F.Neq (l, r)) = F.Neq (renameFunTerm l, renameFunTerm r)

fun toString form =
    let fun paren s = "(" ^ s ^ ")"
	fun rename (F.Atom atom) = F.Atom (renameFun atom)
	  | rename (F.Not p) = F.Not (rename p)
	  | rename (F.And (p, q)) = F.And (rename p, rename q)
	  | rename (F.Or (p, q)) = F.Or (rename p, rename q)
	  | rename (F.Imp (p, q)) = F.Imp (rename p, rename q)
	  | rename (F.Iff (p, q)) = F.Iff (rename p, rename q)
	  | rename (F.All (x, p)) = F.All (x, rename p)
	  | rename (F.Exists (x, p)) = F.Exists (x, rename p)
	fun aux (F.Atom atom) = F.toStringAtom atom
	  | aux (F.Not p) = "-" ^ paren (aux p)
	  | aux (F.And (p, q)) = paren (aux p ^ " & " ^ aux q)
	  | aux (F.Or (p, q)) = paren (aux p ^ " | " ^ aux q)
	  | aux (F.Imp (p, q)) = paren (aux p ^ " -> " ^ aux q)
	  | aux (F.Iff (p, q)) = paren (aux p ^ " <-> " ^ aux q)
	  | aux (F.All (x, p)) = "all " ^ Var.toString x ^ " " ^ paren (aux p)
	  | aux (F.Exists (x, p)) = "exists " ^ Var.toString x ^ " " ^ paren (aux p)
    in (aux o F.toVars o F.toNeq o rename) form
    end

fun makeInFile forms timeout =
    let val outStream = TextIO.openOut "mace.in"
	val _ = TextIO.output (outStream, "assign(max_seconds, " ^ Int.toString timeout ^ ").\n")
	val _ = TextIO.output (outStream, "formulas(theory).\n")
	fun loop [] = ()
	  | loop (line::rest) =
	    let val _ = TextIO.output (outStream, line ^ ".\n")
	    in loop rest
	    end 
	val _ = loop (List.map toString forms)
	val _ = TextIO.output (outStream, "end_of_list.\n")
	val _ = TextIO.closeOut outStream
    in ()
    end

fun runM4 () =
    let val command = "./mace4 -f mace.in > mace.out"
	val _ = OS.Process.system command
	val inStream = TextIO.openIn "mace.out"
	val result = TextIO.inputAll inStream
	val _ = TextIO.closeIn inStream 
    in result
    end

fun findSubstring (s, t) =
    let val n = String.size s
        val m = String.size t
        fun loop i =
            if i + m > n then NONE
            else if String.substring(s, i, m) = t then SOME i
            else loop (i + 1)
    in loop 0
    end

fun extractBetween (str, str1, str2) =
    case findSubstring (str, str1) of
        NONE => NONE
      | SOME i =>
          let val start = i + String.size str1
          in case findSubstring (String.extract(str, start, NONE), str2) of
                 NONE => NONE
               | SOME j => SOME (String.substring(str, i, (start + j + String.size str2) - i))
          end

fun printModel result =
    let val model = case extractBetween (result, "============================== MODEL =================================", "============================== end of model ==========================\n") of
			SOME m =>
			let val _ = print m;
			in true
			end 
		      | NONE => false
    in model
    end

fun mace forms timeout =
    let val _ = print ("model finding using Mace4:\n" ^ Form.prForms forms)
	val _ = makeInFile forms timeout
	val result = runM4 ()
    in if String.isSubstring "Exiting with failure" result
       then
	   let val _ = print "==> FAILURE\n"
	   in false
	   end 
       else
	   let val _ = print "==> SUCCESS\n"
	   in printModel result
	   end 
    end 
end
end
