import React, { useState } from 'react';
import FunctionComponent from './FunctionComponent';
import { Function, FunctionLibraryProps } from './interfaces';

const FunctionLibrary: React.FC<FunctionLibraryProps> = ({ functions, onAdd, onChange }) => {
  const handleAdd = () => {
    const newFunction: Function = { name: '', formula: '' };
    onChange([...functions, newFunction]);
  };

  const handleChange = (index: number, func: Function) => {
    const updatedFunctions = [...functions];
    updatedFunctions[index] = func;
    onChange(updatedFunctions);
  };

  const handleRemove = (index: number) => {
    const updatedFunctions = [...functions];
    updatedFunctions.splice(index, 1);
    onChange(updatedFunctions);
  };

  return (
    <div>
      <button onClick={handleAdd}>Add Function</button>
      {functions.map((func, index) => (
        <FunctionComponent
          key={index}
          func={func}
          onChange={(newFunc) => handleChange(index, newFunc)}
          onRemove={() => handleRemove(index)}
        />
      ))}
    </div>
  );
};

export default FunctionLibrary;
