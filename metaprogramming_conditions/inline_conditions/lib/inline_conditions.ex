defmodule Conditions do
  defmacro defv(call, opts \\ [], do: do_block) do
    # Extract `requires` and `ensures` conditions from the keyword options
    {requires_expr, _opts} = Keyword.pop(opts, :requires)
    {ensures_expr, _opts} = Keyword.pop(opts, :ensures)

    # Generate precondition check
    precondition_check = generate_precondition_check(requires_expr)

    # Generate postcondition check
    postcondition_check = generate_postcondition_check(ensures_expr)

    # Construct the function definition with precondition, function body, and postcondition checks
    quote do
      def unquote(call) do
        # Precondition check
        unquote(precondition_check)

        # Execute the function body and capture the result
        result = unquote(do_block)

        # Postcondition check
        unquote(postcondition_check)

        # Return the result from the function body
        result
      end
    end
  end

  # Function to generate precondition check
  defp generate_precondition_check(requires_expr) when is_nil(requires_expr) do
    quote do
      :ok
    end
  end

  defp generate_precondition_check(requires_expr) do
    quote do
      unless unquote(requires_expr) do
        raise ArgumentError, "Precondition failed: #{inspect(unquote(requires_expr))}"
      end
    end
  end

  # Function to generate postcondition check
  defp generate_postcondition_check(ensures_expr) when is_nil(ensures_expr) do
    quote do
      :ok
    end
  end

  defp generate_postcondition_check(ensures_expr) do
    quote do
      unless unquote(ensures_expr) do
        raise ArgumentError, "Postcondition failed: #{inspect(unquote(ensures_expr))}"
      end
    end
  end
end

# Usage example
defmodule Test do
  import Conditions

  defv test(x), requires: x > 0, ensures: ret == x * x do
    ret = x * x
    IO.inspect ret
    ret
  end
end
