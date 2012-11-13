(* Removes an arbitrary number of negations from the left side of a string *)
fun dropnegation str = 
    if String.substring(str,0,1) = "~" 
    then dropnegation (String.substring(str,1,String.size(str)-1))
    else str;
        
(* Transforms expressions with redundant negations to simplest form. ex. ~~a => a *)
fun simplifynegation str = 
    if String.size(str) > 2 
        andalso String.substring(str,0,1) = "~" 
            andalso String.substring(str,1,1) = "~" 
    then simplifynegation (String.substring(str,2,String.size(str)-2))
    else str;

(* Takes a list of lists and flattens it into one list. *)
fun flatten ( [] ) = [] 
    | flatten ( h::t ) = h @ flatten ( t ) ;

(* Takes and removes an element from a list. *)
fun delete ( del, [] ) = [] 
    | delete ( del, h::t ) = 
        if del = h 
        then delete ( del, t ) else h::delete ( del, t );
    
(* Takes a list and removes any duplicate elements *)
fun removedupes ( [] ) = []     	
    | removedupes ( h::t ) = h::removedupes ( delete ( h, t ) );

(* Given a list of vars and a list of boolean values (corresponding
   to the values for each variable) , this function will merge them
   together into a list of (string,bool) pairs.  We will call this
   merged list a "binding list."  *)
fun createbindinglist ( vhead::vtail, bhead::btail ) = 
      (vhead,bhead)::createbindinglist ( vtail, btail )
    | createbindinglist ( [], [] ) = []
    | createbindinglist ( _, _ ) = [];

(* Given a string variable name and a binding list containing (string,bool), 
   this function will look up the variable in the bindings list and return 
   the second element of the tuple.  *)
fun findvar ( v : string, [] ) = false
    | findvar ( v : string, bhead::btail : (string * bool) list ) = 
        if v = #1 bhead
        then #2 bhead
        else findvar (v, btail);

(*  Given a list of (string,bool) bindings and a clause 
    (list of var exprs), this will return true if the 
	clause is satisfied by the bindings and false otherwise. *)
fun applybindingstoclause ( bindings, [] ) = false 
    | applybindingstoclause ( bindings, chead::ctail ) = 
      let 
        val isnegated = String.substring(simplifynegation(chead),0,1) = "~"
        val isbindingtrue = findvar(dropnegation(chead), bindings)
      in
        (isbindingtrue andalso not isnegated) 
            orelse (not isbindingtrue andalso isnegated) 
                orelse applybindingstoclause (bindings, ctail)          
      end

(*  Given a list of variable bindings and an expression, this will 
    apply the boolean values to the boolean expression and test for 
	satisfiability.  Should make use of applybindingstoclause above. *)
fun applybindingstoexpr ( bindings, [] ) = true  
    | applybindingstoexpr ( bindings, exprhd::exprtail) =
        applybindingstoclause (bindings, exprhd) 
            andalso applybindingstoexpr (bindings, exprtail); 
            
(*  Prints a (string * boolean) tuple. *)
fun printbinding( name : string, value : bool ) = 
    ( print name; print "=";  print (Bool.toString value); print " ");

(* Performs a brute force variable test by attempting
   all possible values of the variables passed in via the
   variable list, vars.  Variable blist is a list of 
   bool, which is treated here as an accumulator (starts
   empty, and each recursive call results in an item added
   to the list). Expr is the entire input CNF expression. *)
fun solve ( vars, blist, expr ) = 
    let 
        (* calling this function every invocation is inefficient, 
           but efficiency is clearly not the goal :) *)
        val bindings = createbindinglist(vars, blist)
    in
        if length(blist) = length(vars) 
        then 
            if applybindingstoexpr( bindings, expr )
            then ( print "\nSolved by bindings( " ; 
                   map printbinding bindings; print ")\n" ;  true )
            else false
        else
            if solve ( vars, blist@[false], expr ) = false 
            then solve ( vars, blist@[true], expr )
            else true
   end

(* Satisfiable according to boolsat.com *) 
val cnf = [
    ["~3", "~~~5", "~7"],
    ["3", "~5", "7"],
    ["~3", "5", "7"],
    ["~3", "~5", "~6"],
    ["3", "~5", "~6"],
    ["3", "5", "~6"],
    ["~3", "~4", "~6"],
    ["~3", "4", "~6"],
    ["~3", "4", "6"],
    ["3", "4", "~~6"],
    ["2", "4", "5"],
    ["2", "~~~4", "5"],
    ["~1", "3", "4"],
    ["~1", "~2", "~4"],
    ["1", "~2", "~4"],
    ["1", "~2", "4"],
    ["1", "2", "3"],
    ["~1", "2", "3"],
    ["1", "~~2", "~3"]
];

val vars = removedupes ( map dropnegation ( flatten ( cnf ) ) );
solve ( vars, [], cnf );
