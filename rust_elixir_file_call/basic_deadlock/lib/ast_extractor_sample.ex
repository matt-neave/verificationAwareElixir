defmodule AstExtractor do
  def main do
    IO.puts("Main called")
    {:ok, ast} = Code.string_to_quoted(File.read!("./lib/delete.ex"))
    File.write!("ast_output.txt", inspect(ast, limit: :infinity)) # Writing AST to a file
    ast
  end
end
