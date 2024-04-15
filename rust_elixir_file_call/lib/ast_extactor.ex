defmodule AstExtractor do
  def main do
    {:ok, ast} = Code.string_to_quoted(File.read!("/mnt/c/Users/matth/Documents/imperial/cw_repos/distributed_cw/multipaxos/lib/acceptor.ex"))
    File.write!("ast_output.txt", inspect(ast, limit: :infinity)) # Writing AST to a file
    ast
  end
end
