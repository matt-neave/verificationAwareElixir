defmodule Verification do
  defmacro def_with_conditions({name, _args, _guard, body} = def, conditions) do
    requires = Keyword.get(conditions, :requires, nil)
    ensures = Keyword.get(conditions, :ensures, nil)

    quote do
      def unquote(name)(unquote(_args)) do
        unquote(validate_requires(requires))
        result = unquote(body)
        unquote(validate_ensures(ensures))
        result
      end
    end
  end

  defp validate_requires(nil), do: []
  defp validate_requires(req) do
    quote do
      if ! unquote(req) do
        raise ArgumentError, "Precondition failed"
      end
    end
  end

  defp validate_ensures(nil), do: []
  defp validate_ensures(ens) do
    quote do
      unless unquote(ens) do
        raise RuntimeError, "Postcondition failed"
      end
    end
  end
end

defmodule Math do
  require Verification

  defmacro __using__(_opts) do
    quote do
      require unquote(__MODULE__)
    end
  end

  defmacro def_with_conditions({name, args, guard, body}, conditions) do
    Verification.def_with_conditions({name, args, guard, body}, conditions)
  end

  defmacro requires(expr) do
    quote do
      unquote(expr)
    end
  end

  defmacro ensures(expr) do
    quote do
      unquote(expr)
    end
  end

  defmacro with_conditions({def, conditions}) do
    Verification.def_with_conditions(def, conditions)
  end
end

defmodule TestMath do
  use Math

  with_conditions add(x, y), requires: x >= 0 && y >= 0, ensures: result >= 0 do
    result = x + y
    result
  end
end
