-- Render every math node as MathML in the HTML editions. The shared HTML
-- emitter passes no math option, so TeX would otherwise reach the reader raw.
local function mathml(el)
  local html = pandoc.write(pandoc.Pandoc({ pandoc.Plain({ el }) }), 'html', { html_math_method = 'mathml' })
  return pandoc.RawInline('html', html:gsub('^%s+', ''):gsub('%s+$', ''))
end

function Math(el)
  return mathml(el)
end
