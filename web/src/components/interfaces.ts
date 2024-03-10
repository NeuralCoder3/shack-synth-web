// Function type
export interface Function {
  name: string;
  formula: string;
}

// Props for the FunctionComponent
export interface FunctionProps {
  func: Function;
  onChange: (func: Function) => void;
  onRemove: null | (() => void);
}

// Props for the FunctionLibrary
export interface FunctionLibraryProps {
  functions: Function[];
  onAdd: () => void;
  onChange: (funcs: Function[]) => void;
}

// State for the FunctionLibrary
export interface FunctionLibraryState {
  functions: Function[];
}