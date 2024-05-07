defmodule Verification do
  defmacro requires(expr) do
    quote do
      if ! unquote(expr) do
        raise ArgumentError, "Precondition failed"
      end
    end
  end

  defmacro ensures(expr) do
    quote do
      case unquote(expr) do
        true -> :ok
        _ -> raise RuntimeError, "Postcondition failed"
      end
    end
  end
end

defmodule Maths do
  require Verification

  def add(x, y) do
    Verification.requires(x >= 0)
    Verification.requires(y >= 0)

    result = x - y
    Verification.ensures(result >= 0)

    result
  end

  def add(x, y), requires: x >= 0 && y >=0, ensures: result >= 0 do
    result = x + y
    result
  end

  @requires x >= 0
  @requires y >= 0
  @ensures result >= 0
  def add(x, y) do
    result = x + y
    result
  end
end
