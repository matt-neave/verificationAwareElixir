defmodule Vae do
  # \\ [] sets default value
  defmacro defv(call, opts \\ [], do: do_block) do
    # Extract `pre` and `post` conditions from the keyword options
    {pre_expr, _} = Keyword.pop(opts, :pre)
    {post_expr, _} = Keyword.pop(opts, :post)

    # Generate precondition check
    precondition_check = generate_precondition_check(pre_expr)

    # Generate postcondition check
    postcondition_check = generate_postcondition_check(post_expr)

    # Construct the function definition with precondition, function body, and postcondition checks
    # Call contains the function name and arguments, when unquoted we create a new kernel function
    # precondition_check contains the AST for an "unless condition: raise error"
    # Similar for postcondition_check
    # We order these, and quote the results to create the final AST returned by the macro
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
  defp generate_precondition_check(pre_expr) when is_nil(pre_expr) do
    quote do
      :ok
    end
  end

  defp generate_precondition_check(pre_expr) do
    quote do
      unless unquote(pre_expr) do
        raise ArgumentError, "Precondition failed: #{inspect(unquote(pre_expr))}"
      end
    end
  end

  # Function to generate postcondition check
  defp generate_postcondition_check(post_expr) when is_nil(post_expr) do
    quote do
      :ok
    end
  end

  defp generate_postcondition_check(post_expr) do
    quote do
      unless unquote(post_expr) do
        raise ArgumentError, "Postcondition failed: #{inspect(unquote(post_expr))}"
      end
    end
  end
end

# Example usage
defmodule Example do
  import Vae

  defv example(x), pre: x > 0, post: ret == x * x do
    ret = x * x
    IO.inspect ret
    ret
  end
end
