defmodule ElixirList do
  @v_entry true
  def start do
    ls = [1,2,3]
    x = Enum.at(ls, 2)
    ls_new = [ls | 4]
    IO.puts head
  end
end
