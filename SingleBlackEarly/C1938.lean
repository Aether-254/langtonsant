import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1938 : checkSingleBlackFast (-69, -46) 20061 .east (32, 17) (9, -51) = true := by
  decide +kernel

end LangtonsAnt
