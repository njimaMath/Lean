-- Preprocess a Lean source file for LaTeX listings in minimal TeX setups.
--
-- Motivation: `listings` cannot reliably apply `literate` substitutions for
-- Unicode codepoints under LuaLaTeX without a full Unicode font setup.
-- This script rewrites common Lean Unicode symbols into ASCII `listings`
-- escape blocks so they render via standard math fonts.

local function read_file(path)
  local handle, err = io.open(path, "rb")
  if not handle then
    texio.write_nl("term and log", ("lean_listing_preprocess: cannot open %s (%s)"):format(path, err))
    return nil
  end
  local data = handle:read("*a")
  handle:close()
  return data
end

local function write_file(path, data)
  local handle, err = io.open(path, "wb")
  if not handle then
    texio.write_nl("term and log", ("lean_listing_preprocess: cannot write %s (%s)"):format(path, err))
    return false
  end
  handle:write(data)
  handle:close()
  return true
end

local replacements = {
  ["ℕ"] = "(*@$\\mathbb{N}$@*)",
  ["ℤ"] = "(*@$\\mathbb{Z}$@*)",
  ["ℝ"] = "(*@$\\mathbb{R}$@*)",
  ["ℙ"] = "(*@$\\mathbb{P}$@*)",
  ["𝓝"] = "(*@$\\mathcal{N}$@*)",
  ["Ω"] = "(*@$\\Omega$@*)",

  ["∀"] = "(*@$\\forall$@*)",
  ["∃"] = "(*@$\\exists$@*)",
  ["∈"] = "(*@$\\in$@*)",
  ["∧"] = "(*@$\\wedge$@*)",
  ["∨"] = "(*@$\\vee$@*)",

  ["→"] = "(*@$\\rightarrow$@*)",
  ["↦"] = "(*@$\\mapsto$@*)",

  ["∂"] = "(*@$\\partial$@*)",
  ["∫"] = "(*@$\\int$@*)",

  ["∞"] = "(*@$\\infty$@*)",
  ["≠"] = "(*@$\\neq$@*)",
  ["≤"] = "(*@$\\leq$@*)",
  ["≥"] = "(*@$\\geq$@*)",
  ["⊤"] = "(*@$\\top$@*)",

  ["⟨"] = "(*@$\\langle$@*)",
  ["⟩"] = "(*@$\\rangle$@*)",

  ["τ"] = "(*@$\\tau$@*)",
  ["ω"] = "(*@$\\omega$@*)",
  ["γ"] = "(*@$\\gamma$@*)",
  ["μ"] = "(*@$\\mu$@*)",

  ["ᵐ"] = "(*@$^m$@*)",
  ["₁"] = "(*@$_1$@*)",
  ["•"] = "(*@$\\bullet$@*)",
  ["⁻"] = "(*@$^-$@*)",
}

function lean_preprocess_listings_utf8(in_path, out_path)
  local data = read_file(in_path)
  if not data then
    return
  end

  for needle, replacement in pairs(replacements) do
    data = data:gsub(needle, replacement)
  end

  write_file(out_path, data)
end

