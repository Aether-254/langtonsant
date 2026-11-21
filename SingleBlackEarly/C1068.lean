import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1068 : checkSingleBlackFast (-14, -4) 38961 .west (2, 1) (-27, -33) = true := by
  decide +kernel

end LangtonsAnt
