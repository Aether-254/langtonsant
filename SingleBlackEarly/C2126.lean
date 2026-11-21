import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2126 : checkSingleBlackFast2 (-86, -58) 18449 .west (36, 42) (-62, 19) = true := by
  decide +kernel

end LangtonsAnt
