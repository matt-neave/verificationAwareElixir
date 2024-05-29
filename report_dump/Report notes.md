The title is too long and does not reflect report. 'Actor based' is hardly mentioned, 'message passing' is more appropriate. In reality, the name of the tool, or 'verification-aware elixir' could be more appropriate.

## Introduction
Talk more about my contribution, why is it non-trivial?
What are verification aware languages.

### Objectives
Reorder them, so that specifications are mentioned first. 'Message passing systems' important here.
Talk about techniques.
Mention we will map elixir -> model checkers like spin.

### Contributions
Can be more specific and detailed than objectives (i.e. the model checker is spin). Featureset of the tools. Diagram of the toolchain (higher level than implementation)

## Background
Mention hybrid systems involving shared memory and message passing.
Needs an introduction, explain why the background is important, what VA is, mention existing languages and other state-of-the-art tools.
What is the alternative to VA? I.e. hand translation, no specification only code ect..
What are the requirements of a good VA tool.
What is needed for Elixir to be VA.
How would theorem proving extend VAE.
Be fair to other model checkers and give examples of PAT, BLAST, PRISM (or we can use a table for comparison by comparing features like LTL, CTL, probabilistic, perf, scalability ect. -- check wikipedia)
Be consistent with italic useage / presentation
Remove theorem proving, mention it in passing.

### 2.4
What can / cant they do > examples. Features / limitations.

Move 2.4.2 to seperate chapter.

If too much space, move elixir / promela chapter to appendix and keep together.

## Project
Examples given at CSP level.
Show diagrams instead of examples.
Provide BNF for LTLixir.
Remove all mix stuff, just mention in text.

4.1 should be deadlock detection, not random elixir code.
All LTLixir syntax should be specially coloured.
Mention the 'class' of deadlock we are detecting.
Type specifications don't really belong in 4 as much as 5.
Show more LTL formula examples (even without code)
Compress examples, remove add_positives and instead just show the built in pre- post- example
Indicate we use bigger examples in evaluation
Mention limitations of syntax because of elixir / spin

## Implementation
Diagram more in depth than intro
Break down big text blocks with diagrams or headings.
Use more bold / italics
Capture more in the summary => explain in depth the recap.
Put promela outputs in line or appendix
Put limitatitons imposed by promela / elixir
Mention perf improvements
Mention it is useful for system evolution / maintence

## Evaluation
Show how paxos can now be extended w total broadcast
Show lots of examples, introduce artificial bugs