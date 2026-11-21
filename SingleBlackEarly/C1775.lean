import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1775 : checkSingleBlackFast (-54, -28) 12316 .north (16, 8) (-42, -24) = true := by
  decide +kernel

end LangtonsAnt
