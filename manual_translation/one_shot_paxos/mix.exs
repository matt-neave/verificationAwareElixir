defmodule OneShotPaxos.MixProject do
  use Mix.Project

  def project do
    [
      app: :one_shot_paxos,
      version: "0.1.0",
      elixir: "~> 1.12",
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger]
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      {:vae_lib, path: "/mnt/c/Users/matth/Documents/imperial/final/metaprogramming_conditions/vae_lib"},
      {:stream_data, "~> 1.0", only: :test}
    ]
  end
end
