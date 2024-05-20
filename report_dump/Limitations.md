
- Extractions of Elixir programs is done on the highest level of the quoted expression. Instead, we can manually traverse the quoted expression to [expand_once/2](https://github.com/elixir-lang/elixir/blob/74bfab8ee271e53d24cb0012b5db1e2a931e0470/lib/elixir/lib/macro.ex#L1439) and resolve abstracted concepts such as libraries, macros into more primitive elixir code.
- Kernel standard library provides various concurrency primitives such as:
	- Agents: processes with mutable state
	- Task: process for computation
	- [And more](https://hexdocs.pm/elixir/1.12.3/Kernel.html) 
	- Ports
	- 
- PRE and POST conditions are NOT solved by an SMT solver. Although every state if checked in an exhaustive approach (DFS), it does not guarantee that for an unbounded representation of the model that the conditions remain to hold.
	- Not being solved by an SMT solver means that the Elixir compiler cannot detect violations of these. To detect property violations at compile time, we can introduce SMT solving capabilities. Property violations can be detected during the runtime and also during the model checking of programs. You may not want to run a critical system to detect these errors.. consideration to be made.
- Weak type inference leads to inextensible code. Elixir is dynamically typed with future type system being developed
- Can't handle failures (fault tolerence)
# Limitations of research

- Concurrency in Elixir has not been reasoned about.
- 