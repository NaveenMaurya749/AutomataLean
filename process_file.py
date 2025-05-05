def process_file(file_name):
    try:
        with open(file_name, 'r') as file:
            lines = file.readlines()
        
        processed_lines = []
        for line in lines:
            if len(line) > 0:  # Check if the line is non-empty
                processed_lines.append(line[2:])  # Remove the first two characters
        
        return processed_lines
    except FileNotFoundError:
        print(f"Error: The file '{file_name}' does not exist.")
        return []

if __name__ == "__main__":
    processed_lines = process_file('AutomataLean/PDAs.lean')
    for line in processed_lines:
        with open('AutomataLean/processed_PDAs.lean', 'w') as output_file:
            for line in processed_lines:
                output_file.write(line)