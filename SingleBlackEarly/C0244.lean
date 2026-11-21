import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0244 : checkSingleBlackFast (-1, -5) 6123 .west (0, 3) (-18, -16) = true := by
  decide +kernel

end LangtonsAnt
