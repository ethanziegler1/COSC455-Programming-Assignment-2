(* Parser Recursive Descent Parser in F# *)


////////////////////////////////////////////////////////////////////////////////////////////////////
// The following is but one of many possible structures. In fact F#/Ocaml has many features that
// make parsing complex grammars pretty easy... but... to understand those requires a much deeper
// understanding of the language than we have/will explored/explore.  Unfortunately, the result is
// that the code will not be nearly as concise or elegant as it could otherwise be. However, if you
// which to explore the additional features of the language, feel free to explore!!!
//
// NOTE: A more concise approach could involve "Active Patterns", but those are a little more
// difficult to understand, especially while still trying to grasp "static patterns".
// https://docs.microsoft.com/en-us/dotnet/fsharp/language-reference/active-patterns
// https://fsharpforfunandprofit.com/posts/convenience-active-patterns/
//////////////////////////////////////////////////////////////////////////////////////////////////////



(* This example uses generic OCaml-compatible syntax where where possible, which is identical in most
   places! There *are* LIBRARY differences between F# and OCaml that necessitate slightly different
   functions to be used for input and output.
  
   If using OCaml instead of F#, check out: https://learnxinyminutes.com/docs/ocaml/
  
   A sample grammar:
   
    <sentence>      ::=  <np> <vp> <np> <sentence_tail>
    <sentence_tail> ::=  <CONJUNCTION> <sentence> | EOS 
    <np>            ::=  ARTICLE <adj_list> NOUN <prep_phrase>  	 
    <adj_list>      ::=  ADJECTIVE <adj_tail> | ε  
    <adj_tail>      ::=  , <adj_list> | ε
    <pp>            ::=  PREPOSITION <np> | ε  
    <vp>            ::=  ADVERB VERB | VERB 
    
    <CONJUNCTION>   ::= and | or
    <ADJECTIVE>     ::= small | tall | slow | fast
    <NOUN>          ::= dog | cat | tree
    <ARTICLE>       ::= a | an | the
    <PREPOSITION>   ::= up | around
    <ADVERB>        ::= quietly | quickly
    <VERB>          ::= chases
*)

// Token Type  (Same as the "Lexer" enum in the Java version)
// !!! Remember "tokens" are "terminals"  ***NOT*** "productions"
//     Terminals are represented by Tokens/Types, productions are represented by functions.
type Token =
    //Start of new Token Set
    | ADJ_SEP
    | READ // read statement  
    | WRITE
    | ARITH_OP
    | REL_OP
    | UNTIL
    | REPEAT
    | IF
    | ELSE
    | THEN
    | ENDIF
    | OPEN_P
    | CLOSE_P
    | ASSIGN
    | FUN_CALL
    | EOF
    | DO
    | WHILE
    | DONE
    | ID of string // Could represent and ID in a more complex language, but for now, just a catch-all for anything else.
     
    // Member (of the type) function to get a token from a lexeme (String)
    static member tokenFromLexeme str =
        match str with
            //Start of New Token Set
            | "," -> ADJ_SEP
            | "read" -> READ
            | "write" -> WRITE
            | "+"| "-" | "*" | "/" -> ARITH_OP
            | "<" | ">" | "==" -> REL_OP
            | "until" -> UNTIL
            | "repeat" -> REPEAT
            | "if" -> IF
            | "else" -> ELSE
            | "then" -> THEN
            | "endif" -> ENDIF
            | "(" -> OPEN_P
            | ")" -> CLOSE_P
            | "=" -> ASSIGN
            | "do" -> DO
            | "while" -> WHILE
            | "<-" -> FUN_CALL
            | "$$" -> EOF
            | "done" -> DONE
            | x -> ID x  // aka, ID

let matchToken (theExpectedToken: Token) theList =
    match theList with
    // resolve to the rest of the list when head is the expected type.
    | head :: tail when head = theExpectedToken -> tail

    // head of list did not match the expected type, so we don't even care about "the rest" (_)
    | head :: _ -> failwithf $"Wrong Type! Expected %A{theExpectedToken} but found %A{head}"

    // Couldn't match anything!
    | _ -> failwithf $"Nothing to match! Expected a list with a head of type %A{theExpectedToken}"



let debugDisplay msg list = 
    // NOTE: the "%A" in the interpolated string will print the whole list,
    // instead of just the first few elements.
    printfn $"{msg}\n\tRemaining List is: %A{list}\n"
    list
// NOTE: The |> operator sends (pipes) the output of one function directly to the next one in line.
// "and" just allows multiple, mutually recursive functions to be defined under a single "let"
let rec parse theList = theList |> program

(* OUR ADDED METHODS

<PROGRAM> ::= <STMT_LIST> $$
<STMT_LIST> ::= <STMT> <STMT_LIST> | ε
<STMT> ::= <ID> <ID_TAIL> | <READ_STMT> | <WRITE_STMT> | <IF_STMT> | <DO_STMT>| <WHILE_STMT>
<ID_TAIL> ::= <FUNC_CALL> | assign
<EXPR> ::= id <EXPR_TAIL> | open_p <EXPR> close_p
<EXPR_TAIL> ::= arith_op <EXPR> | ε
<ARITH_OP> ::= + | - | * | /
<REL_OP> ::= > | < | ==
<COND> ::= <EXPR> <REL_OP> <EXPR>
<ASGIGNMENT> ::= assign <EXPR> 
<READ_STMT> ::= read id
<WRITE_STMT> ::= write expr 
<IF_STMT> ::= <IF> <CONDITION> <THEN> <STMT> <ELSE> <STMT> <ENDIF>
<FUN_CALL> ::= id open_p <PARAM_LIST> close_p
<PARAM_LIST> ::= <EXPR> <PARAM_TAIL>
<PARAM_TAIL> ::= , <PARAM_LIST> | ε
<WHILE_STMT> ::= while <COND> do <STMT_LIST> done
<DO_STMT> ::= do <STMT_LIST> until <COND>
 *)

//<PROGRAM> ::= <STMT_LIST> $$
and program xs =
    xs |> stmt_list |> debugDisplay "Program" |> ``$$`` // Note: ```` is a way to escape reserved words

and ``$$`` =
    function
    | [] -> printfn "Top Of Stack!"; ([] : Token list)
    | reminingElements -> failwithf $"Unprocessed Tokens: {reminingElements}"

//<STMT_LIST> ::= <STMT> <STMT_LIST> | ε
and stmt_list lst =
    match lst with
    | _ :: _ -> lst |> stmt |> stmt_list
    | xs -> xs // ε
    
//<STMT> ::= id <ID_TAIL> | <READ_STMT> | <WRITE_STMT> | <IF_STMT> | <DO_STMT>| <WHILE_STMT>
and stmt lst =
    // For debugging!
    printfn $"In stmt rule: The token list  = %A{lst}" // the is a format specifier will print the whole list

    match lst with
    | ID _ :: xs -> xs |> id_tail
    | READ :: xs -> xs |> read_stmt
    | WRITE :: xs -> xs |> write_stmt
    | IF :: xs -> xs |> if_stmt
    | DO :: xs -> xs |> do_stmt
    | WHILE :: xs -> xs |> while_stmt

    | _ -> failwithf $"Not a valid statement: %A{lst}" // no empty case allowed

//<READ_STMT> ::= read id
and read_stmt  =
    function
    | ID _ :: xs -> xs
    | _ -> failwithf $"Not a valid read stmt"

//<WRITE_STMT> ::= write expr 
and write_stmt  =
    function
    | xs ->
        printfn $"in write stmt" // Again, for debugging.
        xs |> expr

//<ID_TAIL> ::= <FUN_CALL> | assign
and id_tail lst = 
    match lst with
    | FUN_CALL :: xs -> xs |> fun_call
    | ASSIGN :: xs -> xs |> expr
    | _ -> failwithf $"Not a valid ID Tail"

//<EXPR> ::= id <EXPR_TAIL> | open_p <EXPR> close_p
and expr = 
    function
    | ID _ :: xs -> xs |> expr_tail
    | OPEN_P :: xs -> xs |> expr |> matchToken CLOSE_P
    | _ -> failwithf $"Invalid expression"

//<EXPR_TAIL> ::= arith_op <EXPR> | ε
and expr_tail = 
    function 
    | ARITH_OP :: xs -> xs |> expr |> expr_tail
    | xs -> xs

//<COND> ::= <EXPR> REL_OPER <EXPR>
and cond lst =
    lst |> expr |> matchToken REL_OP |> expr

//<IF_STMT> ::= <IF> <CONDITION> <THEN> <STMT> <ELSE>
and if_stmt =
    function
    | xs -> xs |> cond |> matchToken THEN |> stmt |> else_stmt

//<ELSE_STMT> ::= <ELSE> <STMT_LIST> <ENDIF> | <ENDIF>
and else_stmt = function
    | ELSE :: xs -> xs |> stmt_list |> matchToken ENDIF 
    | ENDIF :: xs -> xs
    | _ -> failwithf $"Not a valid else stmt"

//<FUN_CALL> ::= id open_p <PARAM_LIST> close_p
and fun_call = 
    function 
    | ID _ :: OPEN_P :: xs -> xs |> param_list |> matchToken CLOSE_P
    | _ -> failwithf $"Not Valid Function Call"

//<PARAM_LIST> ::= <EXPR> <PARAM_TAIL>
and param_list lst =
    lst |> expr |> param_tail

//<PARAM_TAIL> ::= , <PARAM_LIST> | ε
and param_tail =
    function
    | ADJ_SEP :: xs -> xs |> param_list
    | xs -> xs

//<WHILE_STMT> ::= while <COND> do <STMT_LIST> done
and while_stmt = 
    function
    | xs -> xs |> cond |> matchToken DO |> stmt_list |> matchToken DONE

//<DO_STMT> ::= do <STMT_LIST> until <COND>
and do_stmt = 
    function
    | xs -> xs |> stmt_list |> matchToken UNTIL |> cond



(* **********************************************************************************************
   YOU MAY LEAVE THE FOLLOWING CODE AS IS.  IT IS NOT NECESSARY TO MODIFY IT FOR THIS ASSIGNMENT.
   *********************************************************************************************** *)

(* Get the user input and start parsing *)
open System.Text.RegularExpressions

// NOTE: To make the let assignment be a function that accepts no parameters,
// an "empty tuple" must be accepted in ML/SML/OCaml/F#.
let main () =

    // Convert a list of stings to Tokens:
    //    Split the String (which creates an Array)
    //             -> convert the Array to a List
    //             -> MAP the list of strings into a list of Tokens.
    //
    // (Note, though arrays are a lot like lists, lists are a bit easier to use for the pattern matching.)
    
    // 'mapTokens' is mainly it's own function as an example of the ">>" operator.
    // This just means that the mapTokens function is a combination of the convert
    // to list function and the Map to list function. (No parameters are specified!)
    let mapTokens = Array.toList >> List.map Token.tokenFromLexeme  

    // This is very ".NET" specific. Split is part of the .NET API.        
    let getTokenList (str: string) = Regex.Split(str.Trim(), "\\s+") |> mapTokens

    (* Begin Parsing Process *)
    let startParsing str =
        // Display our list of tokens...
        printfn $"\nInitial String: %s{str}"

        // Try to parse the list of tokens and display the results.
        try
            let tokenList = getTokenList str
            printfn $"Tokens Before Parsing: %A{tokenList}"
            let parsedList = parse tokenList

            if (parsedList.Length > 0) then
                printfn $"Parsing Failed because we have extra tokens! %A{parsedList}"
                printfn $"Extra Tokens:\t%A{parsedList}"
            else
                printfn "Done!"

        // If an exception ("failwith") is thrown, display the error message.
        with Failure msg ->
            printfn $"Error: %s{msg}"

    // Get the user input and start parsing
    let getUserInput () =
        printf "Enter (Space Delimited) String\n=> "
        
        // A case where it's easier to use the .NET ReadLine as opposed to the more restrictive OCaml native variant.        
        System.Console.ReadLine()

    in
    // Get the user input and start parsing
    getUserInput () |>  startParsing |> ignore  // Just ignore the result, as we are just printing results above.



(* EXAMPLE TEST DATA:  the small , slow dog quietly chases the fast cat up a tall tree .     *)

// Execute the main function!
main ()