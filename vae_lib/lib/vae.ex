defmodule Vae do
  @init true
  defmacro init?() do
    quote do
      Module.get_attribute(__MODULE__, :init)
    end
  end
end
