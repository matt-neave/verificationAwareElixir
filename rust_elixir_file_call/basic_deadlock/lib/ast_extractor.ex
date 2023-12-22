defmodule AstExtractor do
  def main do
    IO.puts("Main called")
    {:ok, ast} = Code.string_to_quoted(File.read!("./lib/basic_deadlock.ex"))
    File.write!("ast_output.txt", inspect(ast)) # Writing AST to a file
    ast
  end
end
