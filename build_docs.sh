#!/bin/bash
# Generate HTML docs from markdown using pandoc

set -e

STYLE='
body {
	font-family: sans-serif;
	margin: 0 auto;
	padding: 1em;
	max-width: 900px;
	background-color: #f8faf8;
	line-height: 1.6;
}
code {
	color: #150;
}
th {
	background-color: #f0f2f0;
	font-weight: bold;
}
th, td {
	border-top: 1px solid #aaa;
	border-bottom: 1px solid #aaa;
}
.nav {
	margin-bottom: 1em;
	font-size: 0.9em;
}
'

NAV='<div class="nav">
<a href="index.html">← back to noulith</a>
· <a href="readme.html">README</a>
· <a href="builtins.html">BUILTINS</a>
</div>'

generate_doc() {
	local md_file=$1
	local html_file=$2
	local title=$3

	pandoc "$md_file" \
		--standalone \
		--to html5 \
		--metadata title="$title" \
		--metadata viewport="width=device-width, initial-scale=1.0" \
		--include-in-header <(cat <<EOF
<meta name="theme-color" content="#337722">
<link rel="manifest" href="./manifest.json">
<link rel="icon" type="image/png" sizes="192x192" href="./icon-192.png">
<style>
$STYLE
</style>
EOF
) \
		--include-before-body <(echo "$NAV") \
		--output "$html_file"

	echo "Generated $html_file"
}

generate_doc "README.md" "readme.html" "README"
generate_doc "BUILTINS.md" "builtins.html" "Built-in Functions"
