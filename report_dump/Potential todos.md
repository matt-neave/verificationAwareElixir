- Parameterization: ✅
	- Add an annotation type to allow variables to be classed as "model parameters" along with optional ranges
	- Generate a set of models for combinations of params
- Experiment with auto generated safety and liveness properties
- Experiment with CTL
- Improve the traces produced by results
- Add macros in Elixir to specify if fairness should be applied
	- In TLA+, Lamport uses WF_Vars and SF_Vars to expand to the relevant properties
	- ![[Pasted image 20240515174608.png]]
```
WF_v(A) == 
<>[](ENABLED <<A>>_v) => []<><<A>>_v

SF_v(A) ==
[]<>(ENABLED <<A>>_v) => []<><<A>>_v
```

- Work out what a type system is (check Steffan notes)
	- Explore [static types for Erlang](https://github.com/WhatsApp/eqwalizer)
	- Explore [Elixir type system](https://www.irif.fr/_media/users/gduboc/elixir-types.pdf)
	- Read up on [ADTs](https://medium.com/@tssovi/abstract-data-type-adt-in-python-33e6ce1f961e#:~:text=What%20is%20ADT%3F,totally%20hidden%20from%20the%20user.)
	- Read up on [type checking Elixir](https://www.erlang-solutions.com/blog/type-checking-erlang-and-elixir/)
- Read up on the theorem prover Viper, which supports concurrency and has been used to prove correctness claims about rust 
- Attempt to use @type annotation to create LTL instead of strings
- Implement range ..
- Investigate more flags for Elixir implementation
- Predicate definitions and labels using [definitions](https://spinroot.com/spin/Man/ltl.html).
- Read this:https://spinroot.com/spin/Man/4_SpinVerification.html
- 30 days of elixir https://github.com/seven1m/30-days-of-elixir/tree/master
- Bugfix:
	- LTL header duplicates
	- Whitespace in LTL ✅
	- Parse inline LTL ❌
	- For loop ranges can't be assigned to
	- Multiple LTL formulas
	- Output global values to trail
	- import models boilerplate
	- Prefix functions, and variables with the current module and function scope to remove ambiguity
	- Pass arrays as parameters by nesting them with in another array and passing the index around ✅
		- memory[10] = 10 arrays ✅
		- copy the contents of the array to the next available space in memory ✅
		- pass the index of the copied array ✅
	- Wrap \_\_block\_\_ in { } in promela generators for scope control
	- Generate a variable for every type (to handle dynamic typing)
		- sum_i, sum_b, sum_s for int, bool and string ect.
	- Store declarations until first usage to determine type
	- Receive should receive a message_argument (not an int) and only determine which element to extract when inferred upon
	- Need more goddamn type inference everywhere!!!!!
	- Fairness✅
	- Non-exhaustive searching with DBITSTATE ✅
