signature MAIN =
sig
    val generate: string -> unit
end

    
fun bench label (f : 'a -> 'b) (x: 'a) : 'b =
  let
    val t = Timer.startCPUTimer ()
    val y = f x
    val {usr, ...} = Timer.checkCPUTimer t
  in
    print (label ^ " " ^ Time.toString usr ^ "\n");
    y
  end


structure Main : MAIN =
struct
local
    structure LU = ListUtil
    structure F = Form
in

fun generate filename =
    let val input = F.input filename
    in if bench "inf" Inf.checkInfProp input then Ages.ages input else Mace.mace input 10
    end 
end
end 
