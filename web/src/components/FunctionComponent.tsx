import React from 'react';
import { FunctionProps } from './interfaces';

const FunctionComponent: React.FC<FunctionProps> = ({ func, onChange, onRemove }) => {
  const handleNameChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    onChange({ ...func, name: e.target.value });
  };

  const handleFormulaChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    onChange({ ...func, formula: e.target.value });
  };

  return (
    <div>
      <input
        type="text"
        placeholder="Name"
        value={func.name}
        onChange={handleNameChange}
      />
      <input
        type="text"
        placeholder="Formula"
        value={func.formula}
        onChange={handleFormulaChange}
      />
      {
        onRemove && (
            <button onClick={onRemove}>Remove</button>
        )
      }
    </div>
  );
};

export default FunctionComponent;