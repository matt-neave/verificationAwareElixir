defmodule VaeLib do
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

  defmacro predicate(var_name, condition) do
    # Helper function to extract variable names from the condition AST
    vars = extract_vars(condition)
            |> Enum.map(&({&1, Macro.var(&1, nil)}))
            |> Enum.uniq()

    # Generate code to set each variable to 0
    assigns = for {var, ast_var} <- vars do
      quote do
        unquote(ast_var) = 0
      end
    end

    # Combine the variable assignments with the original condition
    quote do
      unquote_splicing(assigns)
      unquote(var_name) = unquote(condition)
    end
  end

  # Extract variable names from the AST
  defp extract_vars(ast, vars \\ []) do
    case ast do
      {:__block__, _, _} = block ->
        block
        |> Macro.prewalk(vars, &extract_vars/2)
        |> elem(1)

      {var, _, context} when is_atom(var) and is_atom(context) ->
        [var | vars]

      {_, _, args} when is_list(args) ->
        args
        |> Enum.reduce(vars, &extract_vars(&1, &2))

      _ ->
        vars
    end
  end

  def unquote(:"eventually")(value) do
    value
  end

  def unquote(:"always")(value) do
    value
  end

  def unquote(:"until")(value) do
    value
  end

  def unquote(:"waek_until")(value) do
    value
  end

  defmacro left ~> right do
    quote do
      not unquote(left) or unquote(right)
    end
  end

  defmacro left <~> right do
    quote do
      unqoute(left) ~> unquote(right) and unquote(right) ~> unquote(left)
    end
  end

  defmacro ltl(condition) do
    quote do
      :ok
    end
  end
end
