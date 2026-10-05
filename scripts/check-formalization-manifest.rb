#!/usr/bin/env ruby
# Validate formalization.yaml against the repository.
#
# Metadata checks (no Lean): every target names an existing lean_file that contains the
# declaration; the external challenge inventory equals challenges/*/config.json; each workspace
# is complete, on the root toolchain, trusted-only by default, with a Mathlib-only Vocabulary.lean,
# a Challenge.lean importing only Mathlib, and no Statement.lean; config theorem names and permitted
# axioms agree
# with the manifest; every target's challenge theorem is listed; the pinned Comparator tool
# revisions agree with scripts/release-comparator.sh. Each project dependency's version is its
# lakefile rev and its commit is the one locked in lake-manifest.json; project.mathlib and
# external_challenges.mathlib equal the lakefile's Mathlib rev, which is the lockfile's Mathlib
# inputRev; every workspace's lake-manifest.json locks exactly the root manifest's package revisions.
#
# Lean checks (after `lake build`): every lean_name and statement_interface resolves, and every
# target depends on exactly axioms.expected.
#
# Usage: ruby scripts/check-formalization-manifest.rb [--metadata-only]
require 'yaml'
require 'json'
require 'open3'
require 'tempfile'
require 'pathname'

ROOT = Pathname.new(__dir__).parent
LEAN_NAME = /\A[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\z/
metadata_only = ARGV == ['--metadata-only']
abort 'usage: check-formalization-manifest.rb [--metadata-only]' unless ARGV.empty? || metadata_only
Dir.chdir(ROOT)
failures = []

manifest = YAML.safe_load_file('formalization.yaml')
abort 'formalization.yaml must be a mapping' unless manifest.is_a?(Hash)
expected_axioms = manifest.fetch('axioms').fetch('expected')
abort 'axioms.expected must be a nonempty list' unless expected_axioms.is_a?(Array) && !expected_axioms.empty?
targets = manifest.fetch('targets')
abort 'targets must be a nonempty list' unless targets.is_a?(Array) && !targets.empty?
abort 'duplicate target id' unless targets.map { |t| t.fetch('id') }.uniq.length == targets.length
root_toolchain = File.read('lean-toolchain').strip
failures << 'project.lean_toolchain differs from lean-toolchain' \
  unless manifest.fetch('project').fetch('lean_toolchain') == root_toolchain

# Dependencies agree with lakefile.toml and lake-manifest.json (matched by repository URL).
root_lock = JSON.parse(File.read('lake-manifest.json')).fetch('packages')
locked = root_lock.reject { |p| p['type'] == 'path' }.to_h { |p| [p['name'], p['rev']] }
manifest.fetch('project').fetch('dependencies').each do |dep|
  lock = root_lock.find { |p| p['url'] == dep['repository'] }
  if lock.nil?
    failures << "dependency #{dep['name']}: #{dep['repository']} is not in lake-manifest.json"
    next
  end
  failures << "dependency #{dep['name']}: version #{dep['version'].inspect} differs from the locked inputRev #{lock['inputRev'].inspect}" \
    unless dep['version'] == lock['inputRev']
  failures << "dependency #{dep['name']}: commit #{dep['commit'].inspect} differs from lake-manifest.json (#{lock['rev']})" \
    unless dep['commit'] == lock['rev']
end
lakefile_text = File.read('lakefile.toml')
lakefile_revs = lakefile_text.scan(/^\[\[require\]\]\s*\nname = "([^"]+)"\s*\n(?:[^\[\n]*\n)*?rev = "([^"]+)"/).to_h
root_lock.each do |p|
  next unless lakefile_revs.key?(p['name'])
  failures << "lake-manifest.json #{p['name']} inputRev #{p['inputRev'].inspect} differs from lakefile.toml (#{lakefile_revs[p['name']].inspect})" \
    unless p['inputRev'] == lakefile_revs[p['name']]
end
lakefile_mathlib = lakefile_revs['mathlib']
failures << 'lakefile.toml has no Mathlib rev' unless lakefile_mathlib

# Targets.
targets.each do |t|
  id = t.fetch('id')
  # Sanity-check targets are certified by their challenge workspace alone (no library name).
  required = %w[title kind challenge challenge_theorem source statement]
  required += %w[lean_name lean_file] unless t['kind'] == 'sanity-check'
  required.each do |k|
    failures << "#{id}: missing #{k}" unless t[k].is_a?(String) && !t[k].strip.empty?
  end
  [t['lean_name'], t['statement_interface'], t['challenge_theorem']].compact.each do |name|
    failures << "#{id}: invalid Lean name #{name.inspect}" unless name.match?(LEAN_NAME)
  end
  file = t['lean_file'].to_s
  if t['kind'] == 'sanity-check' && t['lean_name'].nil?
    # nothing to resolve in the library
  elsif !File.file?(file)
    failures << "#{id}: lean_file #{file} does not exist"
  else
    # Declarations are written inside their namespace, so match the last name component.
    short = t['lean_name'].to_s.split('.').last
    failures << "#{id}: #{file} does not declare #{short}" \
      unless File.read(file).match?(/^(?:@\[[^\]]*\]\s*)?(?:public |protected )?theorem #{Regexp.escape(short)}\b/)
  end
end

# External challenge inventory.
external = manifest.fetch('comparator').fetch('external_challenges')
entries = external.fetch('entries')
abort 'comparator.external_challenges.entries must be a nonempty list' unless entries.is_a?(Array) && !entries.empty?
abort 'duplicate challenge id' unless entries.map { |e| e.fetch('id') }.uniq.length == entries.length
allowed = external.fetch('permitted_axioms')
failures << 'comparator permitted_axioms differ from axioms.expected' unless allowed.sort == expected_axioms.sort
failures << 'external_challenges.toolchain differs from lean-toolchain' unless external['toolchain'] == root_toolchain
[['project.mathlib', manifest.fetch('project')['mathlib']], ['external_challenges.mathlib', external['mathlib']]].each do |key, rev|
  failures << "#{key} #{rev.inspect} differs from the lakefile's Mathlib rev #{lakefile_mathlib.inspect}" \
    unless rev == lakefile_mathlib
end

listed = entries.map { |e| e.fetch('path') }.sort
on_disk = Dir.glob('challenges/*/config.json').map { |c| File.dirname(c) }.sort
unless listed == on_disk
  failures << "challenge inventory differs from formalization.yaml: " \
              "#{(on_disk - listed).inspect} unlisted, #{(listed - on_disk).inspect} missing"
end

entries.each do |entry|
  path = entry.fetch('path')
  next unless File.directory?(path)
  %w[Vocabulary.lean Challenge.lean Solution.lean config.json lakefile.toml lake-manifest.json lean-toolchain].each do |f|
    failures << "#{path}: missing #{f}" unless File.file?(File.join(path, f))
  end
  failures << "#{path}: Statement.lean is replaced by Vocabulary.lean" \
    if File.exist?(File.join(path, 'Statement.lean'))
  toolchain = File.join(path, 'lean-toolchain')
  failures << "#{path}: lean-toolchain differs from the root" \
    if File.file?(toolchain) && File.read(toolchain).strip != root_toolchain
  workspace_lock = File.join(path, 'lake-manifest.json')
  if File.file?(workspace_lock)
    ws_revs = JSON.parse(File.read(workspace_lock)).fetch('packages')
                  .reject { |p| p['type'] == 'path' }.to_h { |p| [p['name'], p['rev']] }
    failures << "#{path}: lake-manifest.json package revisions differ from the root manifest" \
      unless ws_revs == locked
  end
  # Module files write `public import`/`meta import`; match every form.
  imports = lambda do |f|
    File.file?(f) ? File.read(f).scan(/^\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)/).flatten : []
  end
  %w[Vocabulary.lean Challenge.lean].each do |f|
    failures << "#{path}: #{f} must import Mathlib only" \
      unless imports.call(File.join(path, f)) == ['Mathlib']
  end
  lakefile = File.join(path, 'lakefile.toml')
  if File.file?(lakefile)
    defaults = File.read(lakefile)[/^defaultTargets\s*=\s*\[([^\]]*)\]/, 1].to_s
    failures << "#{path}: Solution must not be a default target" if defaults.include?('Solution')
  end
  config_path = File.join(path, 'config.json')
  next unless File.file?(config_path)
  config = JSON.parse(File.read(config_path))
  failures << "#{path}: theorem_names differ from formalization.yaml" \
    unless config.fetch('theorem_names') == entry.fetch('theorem_names')
  failures << "#{path}: permitted_axioms differ from formalization.yaml" \
    unless config.fetch('permitted_axioms').sort == allowed.sort
  failures << "#{path}: unexpected challenge module" unless config.fetch('challenge_module') == 'Challenge'
  failures << "#{path}: unexpected solution module" unless config.fetch('solution_module') == 'Solution'
end

challenge_theorems = entries.flat_map { |e| e.fetch('theorem_names').map { |n| [e.fetch('path'), n] } }.sort
target_theorems = targets.map { |t| [t['challenge'], t['challenge_theorem']] }.sort
unless challenge_theorems == target_theorems
  failures << "challenge theorems differ from the targets' challenge_theorem fields: " \
              "#{(challenge_theorems - target_theorems).inspect} without a target, " \
              "#{(target_theorems - challenge_theorems).inspect} not in any config"
end

driver = File.read('scripts/release-comparator.sh')
{ 'comparator_revision' => 'COMPARATOR_REV',
  'lean4export_revision' => 'LEAN4EXPORT_REV',
  'landrun_revision' => 'LANDRUN_REV' }.each do |key, var|
  pinned = driver[/^#{var}=(\h+)$/, 1]
  failures << "#{key} #{external[key].inspect} differs from #{var} in scripts/release-comparator.sh" \
    unless pinned && external[key] == pinned
end

abort failures.join("\n") unless failures.empty?
if metadata_only
  puts "Validated #{targets.length} targets and #{entries.length} challenge workspaces (metadata only)"
  exit 0
end

# Lean: one invocation resolves every name and prints the axioms of every target.
lean_targets = targets.reject { |t| t['lean_name'].nil? }
names = lean_targets.flat_map { |t| [t.fetch('lean_name'), t['statement_interface']] }.compact.uniq
Tempfile.create(['manifest-check-', '.lean']) do |file|
  file.puts 'import InnerVariational'
  file.puts 'import Sperner'
  names.each { |n| file.puts "#check @#{n}" }
  lean_targets.each_with_index do |t, i|
    file.puts %Q(#eval IO.println "AXIOMS_BEGIN_#{i}")
    file.puts "#print axioms #{t.fetch('lean_name')}"
    file.puts %Q(#eval IO.println "AXIOMS_END_#{i}")
  end
  file.flush
  output, status = Open3.capture2e('lake', 'env', 'lean', file.path)
  output.force_encoding(Encoding::UTF_8)
  unless status.success?
    warn output
    abort 'Lean name resolution or axiom check failed'
  end
  lean_targets.each_with_index do |t, i|
    name = t.fetch('lean_name')
    section = output[/AXIOMS_BEGIN_#{i}(.*?)AXIOMS_END_#{i}/m, 1]
    abort "missing #print axioms output for #{name}" unless section
    actual = if section.include?('does not depend on any axioms')
               []
             else
               block = section[/depends on axioms: \[([^\]]*)\]/, 1]
               abort "unrecognized #print axioms output for #{name}: #{section}" unless block
               block.split(',').map(&:strip).uniq
             end
    failures << "#{name}: axioms #{actual.sort.inspect}, expected #{expected_axioms.sort.inspect}" \
      unless actual.sort == expected_axioms.sort
  end
end
abort failures.join("\n") unless failures.empty?
puts "Validated #{targets.length} targets (names resolve; axioms exactly #{expected_axioms.sort.inspect}) " \
     "and #{entries.length} challenge workspaces"
