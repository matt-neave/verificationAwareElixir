defmodule Precondition do
  defp do_generate_preconditions(_name, args) do
    quote do
      Enum.map(unquote(args), &generate_precondition(&1))
    end
  end

  defp generate_precondition(_name, {condition}) do
    quote do
      if not unquote(condition) do
        raise ArgumentError, "Precondition failed: #{inspect(unquote(condition))}"
      end
    end
  end

  defmacro pre(condition) do
    generate_precondition(__CALLER__.module, {condition})
  end
end
