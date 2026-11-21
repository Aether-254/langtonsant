import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1755 : checkSingleBlackFast (-53, -25) 33900 .south (9, -1) (-57, -21) = true := by
  decide +kernel

end LangtonsAnt
