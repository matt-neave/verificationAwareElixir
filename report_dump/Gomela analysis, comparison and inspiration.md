![[Pasted image 20240514102955.png]]
Source: gomela paper


Begin parameterization? => automatic / manual bounding of parameters?

The Go library also includes a runtime global deadlock detector and a runtime data-race detector.

Notes from Gomela on spin:
Spin has notably been 10 used to verify multi-threaded Java programs [11] and multithreaded C programs [32]. Our approach is related to other specialised bounded model checkers for C, C++, and Java, e.g., CBMC [1], [15], ESBMC [7], and JBMC [2]. These checkers use symbolic execution techniques (e.g., unrolling loops k times) to detect low-level bugs.

gomela inline higher order functions 👀

Over/under approximation

gomela uses params => generates multiple models based on params, evaluates all models, computes a score to determine the likelihood of an actual bug under a configuration

##### gomela does not support linked lists (dynamic memory) -> VAE DOES!
 (source, gomela paper: We do not support dynamic data-structures (e.g., linked lists) nor struct embedding.)

### Go examples and differences
Go channels can be buffered (makes automatic parameterization simpiler). Source: https://gobyexample.com/channel-buffering. Example of go channel with buffer size of 2: 
```go
messages := make(chan string, 2)
```
Example of go channel buffering:
```go
package main

import (
    "fmt"
    "time"
)

func worker(done chan bool) {
    fmt.Print("working...")
    time.Sleep(time.Second)
    fmt.Println("done")

    done <- true
}

func main() {

    done := make(chan bool, 1)
    go worker(done)

    <-done
}
```
### Thoughts
Parameterization in elixir is not as natural as go
- Parameterization should be done manually, by adding annotations to functions regarding which params should be bounded, specifying some (optional) reasonable bounds and then generating NxM models for N params, M bounds.