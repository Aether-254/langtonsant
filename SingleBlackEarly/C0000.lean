import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0000 : checkSingleBlackFast (0, 0) 10417 .west (1, -1) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
