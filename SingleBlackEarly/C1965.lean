import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1965 : checkSingleBlackFast (-68, -49) 21336 .north (36, 32) (-62, -24) = true := by
  decide +kernel

end LangtonsAnt
