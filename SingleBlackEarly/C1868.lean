import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1868 : checkSingleBlackFast2 (-61, -39) 15897 .west (18, 27) (-47, 7) = true := by
  decide +kernel

end LangtonsAnt
