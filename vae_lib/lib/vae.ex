defmodule Vae do
  @v_entry true
  defmacro v_entry?() do
    quote do
      Module.get_attribute(__MODULE__, :v_entry)
    end
  end
end
