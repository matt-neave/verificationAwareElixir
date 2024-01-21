defmodule IfAst do
	def my_function do
		if 1 < 2 or false do
			"This works"
		else
			"Now this"
		end
	end
end
