import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1600 : checkSingleBlackFast (-39, -12) 23434 .south (3, -13) (-14, -30) = true := by
  decide +kernel

end LangtonsAnt
