#!/usr/bin/env ruby
# frozen_string_literal: true

require "optparse"
require "yaml"

module PalomarMetadata
  SENTINEL = /\ATEMPLATE(?::|\z)/
  REQUIRED_LICENSE = "Apache-2.0"
  REQUIRED_SECTIONS = %w[project classification automation review].freeze

  class ValidationError < StandardError; end

  def self.placeholder_paths(value, path = "$")
    case value
    when Hash
      value.flat_map { |key, child| placeholder_paths(child, "#{path}.#{key}") }
    when Array
      value.each_with_index.flat_map do |child, index|
        placeholder_paths(child, "#{path}[#{index}]")
      end
    when String
      value.lstrip.match?(SENTINEL) ? [path] : []
    else
      []
    end
  end

  def self.validate(path)
    text = File.binread(path).force_encoding(Encoding::UTF_8)
    raise ValidationError, "#{path} must be valid UTF-8" unless text.valid_encoding?

    document = YAML.safe_load(text, permitted_classes: [], permitted_symbols: [], aliases: false)
    raise ValidationError, "#{path} must contain one top-level mapping" unless document.is_a?(Hash)

    missing = REQUIRED_SECTIONS.reject { |section| document[section].is_a?(Hash) }
    unless missing.empty?
      raise ValidationError, "#{path} is missing required mappings: #{missing.join(', ')}"
    end

    unless document["version"] == "v0.4"
      raise ValidationError, "#{path} $.version must be \"v0.4\""
    end
    unless document.dig("project", "license") == REQUIRED_LICENSE
      raise ValidationError, "#{path} $.project.license must be \"Apache-2.0\""
    end

    description = document.dig("project", "description")
    unless description.is_a?(String) && !description.strip.empty? && description.strip.length <= 10_000
      raise ValidationError, "#{path} $.project.description must be nonempty text of at most 10000 characters"
    end

    placeholders = placeholder_paths(document)
    return if placeholders.empty?

    raise ValidationError, "#{path} still contains TEMPLATE values at #{placeholders.join(', ')}"
  rescue Psych::Exception => error
    raise ValidationError, "cannot parse #{path} as YAML: #{error.message.lines.first&.strip}"
  end

  def self.run(arguments)
    parser = OptionParser.new
    paths = parser.parse(arguments)
    raise OptionParser::InvalidArgument, "expected one metadata path" unless paths.length == 1

    validate(paths.fetch(0))
    puts "#{paths.fetch(0)} contains no TEMPLATE values"
    0
  rescue OptionParser::ParseError, ValidationError => error
    warn error.message
    1
  end
end

exit PalomarMetadata.run(ARGV) if $PROGRAM_NAME == __FILE__
