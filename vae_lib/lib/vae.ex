defmodule Vae do
  @vae_init true
  defmacro vae_init?() do
    quote do
      Module.get_attribute(__MODULE__, :vae_init)
    end
  end
end
