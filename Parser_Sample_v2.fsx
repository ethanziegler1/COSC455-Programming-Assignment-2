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