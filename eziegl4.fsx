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
    | NOUN
    | VERB
    | ARTICLE
    | ADJECTIVE
    | ADVERB
    | PREPOSITION
    | COMMA
    | CONJUNCTION
    | EOS // End of Sentence (period, exclamation point, etc.)
    
    //Start of new Token Set
    | ADJ_SEP
    | READ // read statement  
    | LET
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
    | NUMBER //any integer
    | OTHER of string // Could represent and ID in a more complex language, but for now, just a catch-all for anything else.
     
    // Member (of the type) function to get a token from a lexeme (String)
    static member tokenFromLexeme str =
        match str with
            | "," -> COMMA
            | "dog" | "cat" | "tree" -> NOUN 
            | "a" | "an" | "the" -> ARTICLE 
            | "chases" -> VERB 
            | "small" | "tall" | "slow" | "fast" -> ADJECTIVE 
            | "quietly" | "quickly" -> ADVERB 
            | "up" | "around" -> PREPOSITION 
            | "." | "!" | "?" -> EOS
            | "and" | "or" -> CONJUNCTION
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
            | x -> OTHER str  // aka, ID

let matchToken (theExpectedToken: Token) theList =
    match theList with
    // resolve to the rest of the list when head is the expected type.
    | head :: tail when head = theExpectedToken -> tail

    // head of list did not match the expected type, so we don't even care about "the rest" (_)
    | head :: _ -> failwithf $"Wrong Type! Expected %A{theExpectedToken} but found %A{head}"

    // Couldn't match anything!
    | _ -> failwithf $"Nothing to match! Expected a list with a head of type %A{theExpectedToken}"




// NOTE: The |> operator sends (pipes) the output of one function directly to the next one in line.
// "and" just allows multiple, mutually recursive functions to be defined under a single "let"
let rec parse theList = theList |> sentence

// <sentence> : <np> <vp> <np> <sentence_tail>
and sentence lst = lst |> np |> vp |> np |> sentenceTail

// This serves as an example of possible pattern matches that will occur in other places as well.
// <sentence_tail> ::= CONJUNCTION <sentence> | EOS
and sentenceTail =
    function
    // Conjunction followed by the rest of the list
    | CONJUNCTION :: xs -> sentence xs

    // The token is the ONLY thing in the list
    | [ EOS ] ->
        printfn "Parse Successful!!!"
        // Type cannot be infered from and empty list.
        ([]: Token list)

    // The token is the head of the list, but followed by additional elements
    | EOS :: xs -> failwith $"End of sentence marker found, but not at end!\nRemaining Tokens {xs}"

    // Not the token we are expecting, so we don't even care about the rest of the list
    | x :: _ -> failwithf $"Expected EOS but found: {x}"

    // A completely empty list
    | [] -> failwith "Unexpected end of input while processing EOS"


// *** This uses the matchToken function that was defined above.
// <np> ::= ARTICLE <adj_list> NOUN <prep_phrase>
and np =
    function
    | ARTICLE :: xs -> xs |> adjList |> matchToken NOUN |> pp
    | x :: xs -> failwithf $"Expected article, but found {x}.\nremaining tokens: {xs}"
    | [] -> failwith "article should not be empty"


// <adj_list> ::= ADJECTIVE <adj_tail> | ε
and adjList =
    function
    | ADJECTIVE :: xs -> xs |> adjTail
    | xs -> xs // ε is permitted, so just resolve to what was passed if no other match.


// <adj_tail> ::= COMMA <adj_list> | ε
and adjTail =
    function
    | COMMA :: xs -> xs |> adjList
    | xs -> xs // ε is permitted, so just resolve to what was passed if no other match.


// <pp> ::= PREPOSITION <np> | ε
and pp =
    function
    | PREPOSITION :: xs -> xs |> np
    | xs -> xs // ε is permitted, so just resolve to what was passed if no other match.


// <vp> ::=  ADVERB VERB | VERB
and vp =
    function
    | VERB :: xs -> xs
    | ADVERB :: xs -> xs |> matchToken VERB

    // | ADVERB :: VERB :: xs -> xs  // Would be logically equivalent to the previous line.
    // | ADVERB :: xs when (List.head xs = VERB) -> xs  // Would be logically equivalent to the previous line.

    | x :: xs -> failwithf $"Expected Verb Phrase, but found {x}.\nRemaining tokens: {xs}"
    | [] -> failwith "Unexpected end of input while processing Verb Phrase."

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
and program =
    function
    | x :: xs -> xs |> stmt_list |> matchToken = EOF

//<STMT_LIST> ::= <STMT> <STMT_LIST> | ε
and stmt_list = 
    function
    | STMT :: xs -> xs |> stmt_list
    | xs ->
//<STMT> ::= id <ID_TAIL> | <READ_STMT> | <WRITE_STMT> | <IF_STMT> | <DO_STMT>| <WHILE_STMT>
and stmt = 
    function
    | ID :: xs -> xs |> id_tail

//<ID_TAIL> ::= <FUN_CALL> | assign
and id_tail = 
    function
    | x :: xs -> xs |> fun_call
    | ASSIGN

//<EXPR> ::= id <EXPR_TAIL> | open_p <EXPR> close_p
and expr = 
    function
    | ID :: xs -> xs |> expr_tail
    | OPEN_P :: xs -> xs |> expr |> matchToken = CLOSE_P

//<EXPR_TAIL> ::= arith_op <EXPR> | ε
and expr_tail = 
    function 
    | ARITH_OP :: xs -> xs |> expr
    | xs -> xs

//<ARITH_OP> ::= + | - | * | /
and arith_op = 
    function
    | xs -> xs |> matchToken = ARITH_OP

//<REL_OPER> ::= > | < | ==
and rel_op = 
    function
    | xs -> xs |> matchToken = REL_OP

//<COND> ::= <EXPR> <REL_OPER> <EXPR>
and cond =
    function
    | expr :: xs -> xs |> rel_op |> expr

//<ASGIGNMENT> ::= assign <EXPR> 
and assignment =
    function   
    ASSIGN:: xs -> xs |> expr

//<READ_STMT> ::= read id
and read_stmt =
    function 
    |  READ:: xs -> xs |> matchToken = id

//<WRITE_STMT> ::= write expr 
and write_stmt =
    function 
    |  WRITE:: xs -> xs |> matchToken = id

//<IF_STMT> ::= <IF> <CONDITION> <THEN> <STMT> <ELSE> <STMT> <ENDIF>
and if_stmt =
    function 
    | IF :: xs -> xs |> cond |> THEN |> stmt |> ELSE |> stmt |> ENDIF

//<FUN_CALL> ::= id open_p <PARAM_LIST> close_p
and fun_call = 
    function 
    | x :: xs -> xs |> OPEN_P |> param_list |> CLOSE_P

//<PARAM_LIST> ::= <EXPR> <PARAM_TAIL>
and param_list =
    function
    | expr :: xs -> xs |> param_tail

//<PARAM_TAIL> ::= , <PARAM_LIST> | ε
and param_tail =
    function
    | ADJ_SEP :: xs -> xs |> param_list
    | xs -> xs

//<WHILE_STMT> ::= while <COND> do <STMT_LIST> done
and while_stmt = 
    function
    |WHILE :: xs -> xs |> cond |> DO |> stmt_list |> DONE
//<DO_STMT> ::= do <STMT_LIST> until <COND>
and do_stmt = 
    function
    | DO :: xs -> xs |> stmt_list |> UNTIL |> cond

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