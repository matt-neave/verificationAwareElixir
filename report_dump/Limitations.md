
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
- Can't handle failures (fault tolerence) (Erlang has a let it go crash design)
- Can't handle CTL, can't check the existence of a path where each of the consensus values are chosen
# Limitations of research

- Concurrency in Elixir has not been reasoned about.
- Can verify message passing of two sessions using binary session types - https://gerardtabone.com/publications/UoM%20-%20technical%20report%202022.pdf. Real world systems often rely on more than two actors.
- UnitEx -> designed for unit testing, can't be used to specify and reason about properties. Requires developers to think of conditions / executions that could break the system in stead of exhaustive checking -> can miss cases
- property based testing can't handle messages? https://github.com/parroty/excheck

What tools? PropEr, ExUnit, Session types -- struggle with system wide property specification
# Research questions
- Specify system - level properties to provably reason about the entirety of a system
- Model and detect concurrency bugs between more than two processes
- Property based testing too low level, 