defmodule ElixirList do
  @vae_init true
  def start do
    ls = [1,2,3]
    x = Enum.at(ls, 2)
    ls_new = [ls | 4]
    IO.puts head
  end
end
