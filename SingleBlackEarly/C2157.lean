import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2157 : checkSingleBlackFast (-88, -66) 20379 .east (34, 28) (1, -46) = true := by
  decide +kernel

end LangtonsAnt
