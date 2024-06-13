Abstract needs to be much stronger. Sell the achievements
- Doesnt mind a verbose report, but highlight the key factors. Use more italics and bold -- dont overuse them -- but use them to highlight the key phrases!
- ITS GOOD THAT PRE AND POST CONDITIONS WORK AT RUNTIME!!!!!!!!!!!!!!!!!
- Remove all floyd-hoare logic with contract.. mention how floyd-hoare logic was an inspiration...
- Use italics use italics use italics
- @v_entry => @init
- give predicates names
- use contracts going forward instead of floyd-hoare and verified function
- which big tools have been verified? CompSearch (C Compiler)
# Abstract
- not capturing the essence of whats in the project
- promote the notion of distributed algorithms (prototyping..., replacing a specification modelling language with this framework.) 
- Express using properties (safety, liveness)
- Concurrent normally means shared memory=> distributed can highlight message passing
- want to be clear about making the claim on the LANGUAGE or the TOOL! which bit do you care about the most (naranker thinks the language, elixirv). say i touch nothing in the elixir program to make it verification aware - all we require is various bits of information. **Just use the one word (verlixir) for both.** Naranker thinks get rid of LTLixir naming, just run with verlixir.
- "This project proposes and evaluates ElixirV,"

Chapter titles:
Verlixir / Design of Verlixir (4 and 5) could do with re-naming to help with the distinction. Some of the section titles are also more bland... be cooler (can use propose a question). Some best PHDs do: "the problem is the following...". 
example: "Why verification-aware languages?" -- then explain this paradigm of why interlinking is better than separate. 

Look at the wording: rigerous not vigerous!!!!

It's overworded... between sequential nodes ... => sequential processes
# Introduction
- Why distributed ? because of the cloud based things. 
- Naranker lecture slides, lecture 1 have examples of 'why distributed?'. Need to consider these factors ontop of functional correctness
- 'Message passing can be more simple to reason about' -- find a reference. If someone asks me about it, need to be able to quote it.
- Don't need to give the description of Elixir in the introduction. Instead, we want to introduce the project: "we are going to introduce a verification aware programming language for message passing". Currently, too much information. Introduction can instead explicitly say the problem statement. 
- "We introduce Verlixir, an analysis tool"... is verlixir not actually a 'verification-aware language'. Don't flip between modes of phrasing. Just call verlixir a verificaiton-aware language. Even though it's elixir, we argue similar languages can be swapped out for elixir (i.e. Go, CSP). Clarity about what Verlixir is, keep the story around that.
#### Objectives
- Think of goals in a much higher way. Capture the interesting and cool things. create a list of interesting things to talk about, pull from the list into the objectives. 
- Remove the stuff about GO from the introduction. (move them later on)! What ElixirV supports could be interesting in the objectives (highlighted as an overview)
- If global shared memory is mentioned more than once, remove it (at least within a chapter).

#### Contributions
- Need to provide a sense of the challenges that are addressed. be direct / proud of the achievements... help express the problem space. 
- Not sure about the diagram... (just remove it)!


#### Background
- Not sure why the CSP section is used. The notion of actors and message-passing is, but not the formal math. 
- Could compare and contract shared memory and message passing styles (i.e. CSP to shared memory).
- The formal math is never used.
- Explain how Elixir and Go are inspired by CSP.
- CSP should be mentioned, but not formally introduced?
- CSP and Elixir are very different. 
- Would rather focus on the title straight away... verification-awareness and actor based message passing. 

- Solution is verification is typically model checking. But also proof assistants are a solution.
- Concurrency ok. LTL ok. Safety and liveness ok. Fairness ok.

- 'By using both safety and liveness properties, we can define a 'correct' system, through the evaluation of these temporal formulae.' could go at the start too!! very important to the definition of distributed algorithms.

- Didnt explain what probabilistic and concurrent support mean in the model checking section. Explain before / after the table what they mean, why they are relevant.. why some systems care about them. Why the need and want them in wireless sensor networks for example
- PRIMSM sub too short. Bulk it out
- give an example of what PRISM and BLAST can give answers to
-  random distributed algorithms WRONG =>>> should say "randomised distributed algorithms".
- Don't use X discovered Y... use formulate / create / designed ect..
- Forget about TLA, only mention TLA+.
- Say 'for example'!  
- instead of 2.3.2, give it a title (i.e. proof assistants)
- Hoare logic: naranker doesnt understand. Remove hoare logic. My PRE and POST conditions dont really mean the same as his... 
- **Could argue the notion of defv as a CONTRACT like in the CONTRACT PARADIGM! 'design by contract' is the name!, early languages use eiffel by bertrand meyer.**
- Use 'related work' instead of 'existing work'.
- Remove the examples of dafny, lean ect.
- Dont bother with the forall quantifer.... get rid of the listings....

- Gomela deserves it's own section... move the introduction part on Gomela to it's own "related work" section.

- Add design by contract to related work too. Add more about proof assitants to related work. We can remove 'Additional Verication Techniques' and push proof assisants and contracts to related.

# Chapter 3
- Doesn't like the title. 
- It's a primer on Elixir and Promela.
- Mention parts of Elixir that aren't supported?
- Call the chapter **'Elixir and Promela'**
- Talk about unsupported features for both tools. (Liven some interest).
- Add more to the Promela chapter. Talk about arrays ect... talk about things it has and I won't use.
- Control flow example is not good. Give a concrete example instead of the half baked one.
- Add else to the if statement.
- Show a DO too.
- Talk about how else is a negation of all the truths of the other ifs.
- Put both side by side! (if and do)
- Put !! and ?? in the chapter.
- Add active proctypes, atomic (don't need their own sections)
- Mention what parts have been built into promela and what parts are pure limitations. At the end mention the key limitations that I have extended!

- Go through the language first and then the implementation? (PUSH 3.2.2 FIRST!!!!!!!!!!!!!!!!!)
- Swap the order of the 3.2.2 and the intro / 3.2.1!!! want language features!!!!!!!!!!! 
- Mention extra unsupported features!!!!!!!!!!!!!!1
- Node.spawn is not relevant???????? wtf (talk about the elixir toolchain)
- **3.2.1 SHOULD be in the BACKGROUND!!!!!!!** 
- If the elixir chapter becomes short, it could move into the subsequent chapter or the background chapter.

- **Give the example of a promela program from the Promela manual. (Not one I care about)**
- **Similar for Elixir, show an Elixir program (not one I care about) to give examples of what these things look like. (could put the client server one)... or one from a book / the website..... could show half a page example and mention a few things about it alongside some discussion.** 3/4s of a page for each example.
# Chapter 4

- Want to talk about ElixirV, the verification aware version.
- Too verbose.
- The verifiable feature set could appear in chapter 4... whereas chapter 3 covers more general elixir...
- any programs written in this style,,, we can automatically detect deadlocks for ANY program with ONE line... free of charge!
REstructure:
- mention the feature set
- this is a useful feature set to build distributed algorithms
- can capture all async communication, or free (Without doing anything)
- go into the example with 3 clients and 1 server
- introduce both modes (simulation and verification)
- feasible to do some simulation with randomness
- 3 modes of operation for the tool. 
- include all this in the introduction to the chapter, then build up the examples!!!!!!
- By chapter 5,we should know everything...!
- too verbose, cut down.
- the simple examples can be short af
- **SELL simulator mode!**
- SELL the MODES!!
- explanations need a bit shortering
- **function types deserver their own section**!!!!!!!1
- **TYPES should be in the verifiable feature set!!!**
- mention how types are a requirement
- **REMOVE THE ADD EXAMPLE**
- Wants to see the check\_clients code too! good example of recursion!
- Move types to own section( could go into the chapter 3, mention its a requirement)!!!!!!!!!!! mentioned theyre not used by the elixir compiler, but they are used by special tools like elixirV and dialyzer.
- Remove the "generating trace"... or show "..." and "mention why the trace is omitted".
- predicate p => all\_alive
- predicate q STUPID GET RID OF IT
- Show an example of a "quorum" predicate where "maj >= n / 2"
- add a post condition to show rounds decreasing instead of the dumb add function
- put trace omitted
- simplify the start\_client function, no need to assign LOL
- **Put the deafult -p value in** to make it very clear
- highlight the three modes... make the param version more interesting!!!!!!
- make the modes more explicit. Place in the evaluation the three modes of simulation / evaluation / parameteriation
- @params => @model?
- **Delete the acceptance confidence from the codebase.**
- -p 2


# Chapter 5
- Sometimes wording was changed / heading was changes. some stuff referred to previous stuff ... sometimes things are repetititve... too much text
- Just give intuition
- Spec doesn't appear enough (i.e. is metaprogramming used?)
- bigger picture stuff is ok
- design diagrams should use boxes for the components labelled arrows for information passing
- "The" Elixir Compiler, Include the VaeLib in The Elixir Compiler. "Verlixir Translator". Label promela model, elixir program... Verlixir gets COMMAND LINE INPUTS / ELIXIR FILE / SPECIFICATION .... SPIN gets MY PROMELA LIBRARY / PROMELA CODE ......
- Label the SPIN MODEL CHECKER in diagram
- diagrams should highlight the approach

- Show less concrete side by sides of translations?
- Can i add more diagrams / more fragments of code instead of lots of text
- **DONT CALL THEM ATTRIBUTES. JUST NAME THEM.**
- Think about it as a slidedeck!
- The design needs to be woven in
- Need to explain where meta programming is used, where rust is used.
- Split the flow: upto the promela generator, is most of the information.... we do all the metaprogramming / rust IR first... and then codegen into a separate chapter????????
- dont overelaborate on textual description
- rename the pre and post- example as my own intermediate representation.
- SHOW MORE OF THE PRE AND POST TURNSTILES FOR INTERMEDIATE REPRESENTATION
- dont show the intermediate representation
- maybe put the pest into the appendix
- dont explain what things are in chap5, ensure thats all done in chap4
- Move contracts (in the mapping table) up towards other functions haha
- Remention what !! and ?? are in the table
- Restructure low level information -> highlight the key factor and then go more detail
- Combine 5.3.4 with previous entry
- Simulation / verification
- In the example in 4.5, show a better LTL example? use an exmaple where maj >= n/2 must always hold? (including renaming of p q r and s)
- add \_\_ to all privates
- Explain why !! and ?? in more detail!
- talk about weak fairness can be invoked / handled
- just show examples of the fairness and the strongfairness 

# Evaluation
collect the examples, into a table to show what has been processed.
show promela and elixir for all in appendix.
think of a good table / comparison
call raft, raft election instead of consensus
use 1 and 2 instead of one and two

put performance before translation

not translation reults => comparison!

---forward---  optimisations


# Conclusion
Repeat everything we aimed to achieve in the conclusions(dont just reference them)

Lots of stuff in conclusions... reference everything we aimed to do, what we have done ect.!!


APPENDIX FOR EACH ALGORITHM!
